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

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let rec list_init i n f = if i >= n then [] else (f i) :: (list_init (i + 1) n f) 

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
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
      (match expr with
      | Const n  -> (st, i, o, Some (Value.of_int n))
      | Array a  -> let (st, i, o, res) = eval_list env conf a in
                    (st, i, o, Some (Value.of_array res))
      | Sexp (s, vs) -> let (st, i, o, res) = eval_list env conf vs in
                        (st, i, o, Some (Value.sexp s res))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Var   x -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y) -> let ((st, i, o, Some r1) as conf) = eval env conf x in 
                            let ((st, i, o, Some r2) as conf) = eval env conf y in
                            (st, i, o, Some (Value.of_int @@ to_func op (Value.to_int r1) (Value.to_int r2)))
      | Call (f, params) -> let (st, i, o, eval_params) = eval_list env conf params in
                            env#definition env f eval_params conf
      | Elem (e, idx)    -> let (st, i, o, Some eval_idx) = eval env conf idx in
                            let (st, i, o, Some v) = eval env (st, i, o, None) e in
                            (st, i, o, Some (match v with
                                | Value.Array list -> List.nth list @@ Value.to_int eval_idx
                                | Value.String s -> Value.of_int @@ Char.code @@ String.get s @@ Value.to_int eval_idx))
      | Length e         -> let (st, i, o, Some v) = eval env conf e in
                            (st, i, o, Some (match v with
                                | Value.Array list -> Value.of_int @@ List.length list
                                | Value.String s -> Value.of_int @@ String.length s)))

    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
         secondary);
      
      secondary: p:primary r:("[" i:parse "]" {`Elem i} | "." "length" {`Length})*
            { List.fold_left (fun p x -> match x with 
                | `Elem i -> Elem (p, i)
                | `Length -> Length p
            ) p r };
      
      primary:
        n:DECIMAL {Const n}
      | c:CHAR    {Const (Char.code c)}
      | s:STRING  {String (String.sub s 1 (String.length s - 2))}
      | "[" es:!(Util.list0 parse) "]" { Array es }
      | "`" x:IDENT body:(-"(" !(Util.list parse) -")")? {Sexp (x, default [] body)}
      | x:IDENT p:("(" params:!(Util.list0 parse) ")" {Call (x, params)} | empty {Var x}) {p}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:
            "`" x:IDENT body:(-"(" !(Util.list parse) -")")? {Sexp (x, default [] body)}
          | "_" {Wildcard}
          | x:IDENT {Ident x}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec matches patt value = match patt, value with
        | Pattern.Wildcard, _ -> true
        | Pattern.Ident _, _ -> true
        | Pattern.Sexp (tag, patts), Value.Sexp (rtag, values) ->
            tag = rtag && List.for_all2 matches patts values
        | Pattern.Sexp (_, _), _ -> false

    let rec make_bindings' (s, xs) patt value = match patt with
        | Pattern.Wildcard        -> s, xs
        | Pattern.Ident x         -> (fun y -> if x = y then value else s y), x::xs
        | Pattern.Sexp (_, patts) -> match value with | Value.Sexp (_, values) ->
                                     List.fold_left2 make_bindings' (s, xs) patts values

    let make_bindings patt value = make_bindings' (State.undefined, []) patt value

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
(* Assign *)        | Assign (x, is, e)  -> let (st, i, o, Some v) as conf = Expr.eval env conf e in
                                            let (st, i, o, is) = Expr.eval_list env (st, i, o, None) is in 
                                            let conf = (update st x v is, i, o, None) in
                                            eval env conf Skip k
(* Seq *)           | Seq    (s1, s2)    -> eval env conf (s2 <*> k) s1
                    | If     (e, s1, s2) -> let ((_, _, _, Some v) as conf) = Expr.eval env conf e in
(* IfTrue *)                                if Value.to_int v != 0 then eval env conf k s1 
(* IfFalse *)                               else eval env conf k s2
                    | While  (e, s)      -> let ((_, _, _, Some v) as conf) = Expr.eval env conf e in 
(* WhileTrue *)                             if Value.to_int v != 0 then eval env conf (stmt <*> k) s
(* WhileFalse *)                            else eval env conf Skip k
                    | Repeat (s, e)      -> eval env conf (While (not e, s) <*> k) s
                    | Case (e, branches) -> let (st, i, o, Some v) as conf = Expr.eval env conf e in
                                            let rec processBranches value = function
                                                | (patt, body) :: rest ->
                                                    if matches patt value then
                                                        let s, xs = make_bindings patt value in
                                                        let st = State.push st s xs in
(* CaseMatch *)                                         eval env (st, i, o, None) (Leave <*> k) body
                                                    else
                                                        processBranches value rest
(* CaseNotMatch *)                              | [] -> eval env conf Skip k
                                            in
                                            processBranches v branches
(* Call *)          | Call   (f, params) -> let step (conf, list) e = (let ((_, _, _, Some v) as conf) = Expr.eval env conf e in conf, list @ [v]) in 
                                            let conf, eval_params = List.fold_left step (conf, []) params in 
                                            let conf = env#definition env f eval_params conf in
                                            eval env conf Skip k
                    | Return r           -> (match r with
(* ReturnEmpty *)                             | None   -> (st, i, o, None)
(* Return *)                                  | Some e -> Expr.eval env conf e)
                    | Leave              -> let st = State.drop st in
(* Leave *)                                 eval env (st, i, o, None) Skip k
         
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"skip" {Skip}
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
      | %"case" e:!(Expr.parse) %"of"
            branches:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)]
        %"esac" {Case (e, branches)}
      | x:IDENT idx:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse)    {Assign (x, idx, e)}
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))