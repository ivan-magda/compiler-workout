open GT
open Syntax.Expr
open Syntax.Stmt       
       
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
type config = int list * Syntax.Stmt.config

let evalInsn config instr = match config, instr with
	| (y::x::stack, config),         BINOP op -> ((Syntax.Expr.binop op x y)::stack, config)
	| (stack, config),               CONST z  -> (z::stack, config)
	| (stack, (state, z::inp, out)), READ     -> (z::stack, (state, inp, out))
	| (z::stack, (state, inp, out)), WRITE    -> (stack, (state, inp, out @ [z]))
	| (stack, (state, inp, out)), 	 LD x     -> (state x)::stack, (state, inp, out)
	| (z::stack, (state, inp, out)), ST x     -> (stack, ((Syntax.Expr.update x z state), inp, out))

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config prg = match config, prg with
	| config, instr::prg -> eval (evalInsn config instr) prg
	| config, [] -> config

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpr = function
	| Const x -> [CONST x]
	| Var z -> [LD z]
	| Binop (op, lhs, rhs) -> compileExpr lhs @ compileExpr rhs @ [BINOP op]

let rec compile = function
        | Read z -> [READ; ST z]
	| Write e -> compileExpr e @ [WRITE]
	| Assign (z, e) -> compileExpr e @ [ST z]
	| Seq (z, e)  -> compile z @ compile e
