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
    let empty = {
        g = (fun x -> failwith @@ Printf.sprintf "Unbound global variable %s" x); 
        l = (fun x -> failwith @@ Printf.sprintf "Unbound local variable %s" x); 
        scope = []
    }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v {g; l; scope} = if List.mem x scope then
        {g; l = (fun y -> if x = y then v else l y); scope}
    else
        {g = (fun y -> if x = y then v else g y); l; scope}
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval {g; l; scope} x = if List.mem x scope then l x else g x

    (* Creates a new scope, based on a given state *)
    let enter {g; l; _} xs = {g; l; scope = xs}

    (* Drops a scope *)
    let leave {g; _; _} {_; l; scope} = {g; l; scope}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
      | x:IDENT   {Var x}
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt = match stmt with
      | Read    x          -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e          -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)      -> (State.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2)    -> eval env (eval env conf s1) s2
      | Skip               -> conf
      | If     (e, s1, s2) -> if Expr.eval st e != 0 then eval env conf s1 else eval env conf s2
      | While  (e, s)      -> if Expr.eval st e != 0 then eval env (eval env conf s) stmt else conf
      | Repeat (s, e)      -> let (st_, i_, o_) as conf_ = eval env conf s in 
                                if Expr.eval st_ e == 0 then eval env conf_ stmt else conf_
      | Call   (f, params) -> let eval_params = List.map (Expr.eval st) params in
                              let (params, locals, body) = env#definition f in
                              let sub_state = State.enter st (params @ locals) in
                              let updater = (fun state param value -> State.update param value state) in
                              let ready_sub_state = List.fold_left2 updater sub_state params eval_params in 
                              let (new_state, new_i, new_o) = eval env (ready_sub_state, i, o) body in
                              (State.leave new_state st, new_i, new_o) 

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
      parse: %"fun" name:IDENT "(" params:!(Util.list)[ostap (IDENT)]? ")" 
             locals:(%"local" !(Util.list)[ostap (IDENT)])? "{" body:!(Stmt.parse) "}" 
             {(name, (default [] params, default [] locals, body))}
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
    let m = List.fold_left (fun map (name, def) -> M.add name def map) M.empty defs in 
    let (_, _, o) = Stmt.eval (object method definition f = M.find f m end) (State.empty, i, []) body in o
    
(* Top-level parser *)
ostap (
    parse: !(Definition.parse)* !(Stmt.parse)
)