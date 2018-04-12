(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let default x opt = match opt with
        | Some v -> v
        | None   -> x
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                              
    let to_func op lhs rhs =
      let bti b = if b then 1 else 0 in
      let itb i = if i = 0 then false else true in
      match op with
      | "+"  -> lhs + rhs
      | "-"  -> lhs - rhs
      | "*"  -> lhs * rhs
      | "/"  -> lhs / rhs
      | "%"  -> lhs mod rhs
      | "<"  -> bti (lhs < rhs)
      | "<=" -> bti (lhs <= rhs)
      | ">"  -> bti (lhs > rhs)
      | ">=" -> bti (lhs >= rhs)
      | "==" -> bti (lhs = rhs)
      | "!=" -> bti (lhs <> rhs)
      | "&&" -> bti (itb lhs && itb rhs)
      | "!!" -> bti (itb lhs || itb rhs)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n -> n, conf
      | Var   x -> State.eval st x, conf
      | Binop (op, x, y) -> let r1, ((st, i, o, r) as conf) = eval env conf x in 
                            let r2, ((st, i, o, r) as conf) = eval env conf y in
                            to_func op r1 r2, conf
      | Call (f, params) -> let step (conf, list) e = (let v, conf = eval env conf e in conf, list @ [v]) in 
                            let conf, eval_params = List.fold_left step (conf, []) params in
                            let ((st, i, o, r) as conf) = env#definition env f eval_params conf in 
                            (match r with None -> failwith "Function returned nothing" | Some v -> v), conf
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr 
             (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
        `Lefta, ["!!"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
              |] 
         )
         primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT p:("(" params:!(Util.list0 parse) ")" {Call (x, params)} | empty {Var x}) {p}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a continuation and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
      let (<*>) a b = match a, b with
          | Skip, s -> s
          | s, Skip -> s
          | s1, s2  -> Seq (s1, s2)
      in
      let not e = Expr.Binop ("==", e, Expr.Const 0) in
      match stmt with
(* SkipSkip *)      | Skip               -> if k = Skip then (st, i, o, None)
(* Skip *)                                  else eval env conf Skip k
(* Assign *)        | Assign (x, e)      -> let v, (st, i, o, _) = Expr.eval env conf e in 
                                            let conf = (State.update x v st, i, o, None) in
                                            eval env conf Skip k
(* Write *)         | Write   e          -> let v, (st, i, o, _) = Expr.eval env conf e in 
                                            let conf = (st, i, o @ [v], None) in
                                            eval env conf Skip k
(* Read *)          | Read    x          -> let conf = (match i with z::i' -> (State.update x z st, i', o, None) | _ -> failwith "Unexpected end of input") in
                                            eval env conf Skip k
(* Seq *)           | Seq    (s1, s2)    -> eval env conf (s2 <*> k) s1
                    | If     (e, s1, s2) -> let v, conf = Expr.eval env conf e in
(* IfTrue *)                                if v != 0 then eval env conf k s1 
(* IfFalse *)                               else eval env conf k s2
                    | While  (e, s)      -> let v, conf = Expr.eval env conf e in 
(* WhileTrue *)                             if v != 0 then eval env conf (stmt <*> k) s
(* WhileFalse *)                            else eval env conf Skip k
                    | Repeat (s, e)      -> eval env conf (While (not e, s) <*> k) s 
(* Call *)          | Call   (f, params) -> let step (conf, list) e = (let v, conf = Expr.eval env conf e in conf, list @ [v]) in 
                                            let conf, eval_params = List.fold_left step (conf, []) params in 
                                            let conf = env#definition env f eval_params conf in
                                            eval env conf Skip k
                    | Return r           -> match r with
(* ReturnEmpty *)                             | None   -> (st, i, o, None)
(* Return *)                                  | Some e -> let v, (st, i, o, _) = Expr.eval env conf e in (st, i, o, Some v)

    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"read" "(" x:IDENT ")"          {Read x}
      | %"write" "(" e:!(Expr.parse) ")" {Write e}
      | %"skip" {Skip}
      | %"while" e:!(Expr.parse) %"do" t:parse %"od" {While (e, t)}
      | %"for" t1:parse "," e:!(Expr.parse) "," t2:parse %"do" t3:parse %"od" {Seq (t1, While (e, Seq (t3, t2)))}
      | %"repeat" t:parse %"until" e:!(Expr.parse) {Repeat (t, e)}
      | %"return"  e:(!(Expr.parse))? {Return e}
      | %"if" e:!(Expr.parse) %"then" t:parse 
        elifs:(%"elif" !(Expr.parse) %"then" parse)* 
        elseb:(%"else" parse)? %"fi"
        { 
          let elseBody = match elseb with
            | Some t -> t
            | None -> Skip
          in
          let newElseBody = List.fold_right (fun (e_, t_) t -> If (e_, t_, t)) elifs elseBody in
          If (e, t, newElseBody)
        }
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | name:IDENT "(" params:(!(Util.list)[ostap (!(Expr.parse))])? ")" {Call (name, default [] params)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))