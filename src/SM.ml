open GT       
open Language
open Language.Expr
open Language.Stmt

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let evalInsn config insn = match config, insn with
	| (y::x::stack, conf),   (BINOP op) -> ((Language.Expr.binop op x y)::stack, conf)
	| (stack, conf),         (CONST x)  -> (x::stack, conf)
	| (stack, (s, x::i, o)), READ       -> (x::stack, (s, i, o))
	| (x::stack, (s, i, o)), WRITE      -> (stack, (s, i, o @ [x]))
	| (stack, (s, i, o)),    (LD z)     -> ((s z)::stack, (s, i, o))
	| (x::stack, (s, i, o)), (ST z)     -> (stack, (Language.Expr.update z x s, i, o))

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config prg = match prg with
	| insn::prg -> eval (evalInsn config insn) prg
	| []        -> config
;;

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o;;

let rec compileExpr expr = match expr with
	| Const x            -> [CONST x]
	| Var z              -> [LD z]
	| Binop (op, e1, e2) -> compileExpr e1 @ compileExpr e2 @ [BINOP op]
;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt = match stmt with
	| Read z        -> [READ; ST z]
	| Write e       -> compileExpr e @ [WRITE]
	| Assign (z, e) -> compileExpr e @ [ST z]
	| Seq (t1, t2)  -> compile t1 @ compile t2
;;