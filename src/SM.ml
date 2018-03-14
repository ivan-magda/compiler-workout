open GT
open Syntax
open List
       
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

let evalOperation (stack, (state, i, o)) operation = match operation with
    | BINOP operation -> let (x :: y :: rest) = stack in
                         let binaryResult = Expr.eval state (Expr.Binop (operation, (Expr.Const y), (Expr.Const x))) in
                         (binaryResult :: rest, (state, i, o))
    | CONST x -> (x :: stack, (state, i, o))
    | READ    -> let (x :: rest) = i in (x :: stack, (state, rest, o))
    | WRITE   -> let (x :: rest) = stack in (rest, (state, i, x :: o))
    | LD x    -> ((state x) :: stack, (state, i, o))
    | ST x    -> let (h :: rest) = stack in (rest, (Expr.update x h state, i, o))

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config program = match program with
    | [] -> config
    | l  -> let (operation :: rest) = l in eval (evalOperation config operation) rest

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpression expression = match expression with
    | Expr.Const c                 -> [CONST c]
    | Expr.Var x                   -> [LD x]
    | Expr.Binop (operation, l, r) -> (compileExpression l) @ (compileExpression r) @ [BINOP operation]

let rec compile statement = match statement with
    | Stmt.Read x                 -> [READ; ST x]
    | Stmt.Write expression       -> (compileExpression expression) @ [WRITE]
    | Stmt.Assign (x, expression) -> (compileExpression expression) @ [ST x]
    | Stmt.Seq (s, t)             -> (compile s) @ (compile t)