(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let binop op lhs rhs = 
      let intToBool value = if value = 0 then false else true
      and boolToInt value = if value then 1 else 0
      in match op with
      	| "+" -> lhs + rhs
        | "-" -> lhs - rhs
        | "*" -> lhs * rhs
        | "/" -> lhs / rhs
        | "%" -> lhs mod rhs
        | ">" -> boolToInt (lhs > rhs)
        | "<" -> boolToInt (lhs < rhs)
        | ">=" -> boolToInt (lhs >= rhs)
        | "<=" -> boolToInt (lhs <= rhs)
        | "==" -> boolToInt (lhs = rhs)
        | "!=" -> boolToInt (lhs <> rhs)
        | "!!" -> boolToInt ((intToBool lhs) || (intToBool rhs))
        | "&&" -> boolToInt ((intToBool lhs) && (intToBool rhs))
        | _ -> failwith @@ Printf.sprintf "Unknown operator %s" op

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval state expr = match expr with
    	| Const x -> x
    	| Var z -> state z
    	| Binop (op, left, right) ->
    		let lhs = eval state left
    		and rhs = eval state right in
    		binop op lhs rhs

    let ostapBinOpsList ops = List.map (fun op -> (ostap ($(op)), fun lhs rhs -> Binop(op, lhs, rhs))) ops

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
    	primary: x:IDENT {Var x} | x:DECIMAL {Const x} | -"(" parse -")";
    	parse: !(Ostap.Util.expr
               (fun x -> x)
               [|
                 `Lefta, ostapBinOpsList ["!!"];
                 `Lefta, ostapBinOpsList ["&&"];
                 `Nona,  ostapBinOpsList [">="; ">"; "<="; "<"; "=="; "!="];
                 `Lefta, ostapBinOpsList ["+"; "-"];
                 `Lefta, ostapBinOpsList ["*"; "/"; "%"]
               |]
               primary
        )
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config stmt = match config, stmt with
        | (s, z::i, o), Read var -> (Expr.update var z s, i, o)
        | (s, i, o), Write e -> (s, i, o @ [Expr.eval s e])
        | (s, i, o), Assign (var, e) -> (Expr.update var (Expr.eval s e) s, i, o)
        | conf, Seq (a, b) -> eval (eval conf a) b
        | _, Read _ -> failwith "Empty input stream"

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      stmt:
          -"read" -"(" s: IDENT -")" {Read s}
      	| -"write" -"(" e: !(Expr.parse) -")" {Write e}
      	| s: IDENT -":=" e: !(Expr.parse) { Assign (s, e) };
      seq: left:stmt -";" right:parse { Seq (left, right) }
    )  
      
end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
