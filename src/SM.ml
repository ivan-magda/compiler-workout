open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
 | [] -> conf
 | insn :: prg' -> 
   match insn with
     | JMP s       -> eval env conf (env#labeled s)
     | CJMP (f, s) -> let x::stack' = stack in 
                      let predicate = match f with
                       | "z"  -> (==) 0
                       | "nz" -> (!=) 0
                    in
                    if predicate x then eval env conf (env#labeled s) else eval env conf prg'
         | _ -> eval env
        (match insn with
         | BINOP op -> let y::x::stack' = stack in (Expr.to_func op x y :: stack', c)
         | READ     -> let z::i'        = i     in (z::stack, (st, i', o))
         | WRITE    -> let z::stack'    = stack in (stack', (st, i, o @ [z]))
         | CONST i  -> (i::stack, c)
         | LD x     -> (st x :: stack, c)
         | ST x     -> let z::stack'    = stack in (stack', (Expr.update x z st, i, o))
         | LABEL s  -> conf
        ) prg'

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

class env =
 object (self)
   val mutable label = 0

   method next_label = let last_label = label in
     label <- label + 1; Printf.sprintf "L%d" last_label
 end

let rec compile' env =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)   -> compile' env s1 @ compile' env s2
  | Stmt.Read x         -> [READ; ST x]
  | Stmt.Write e        -> expr e @ [WRITE]
  | Stmt.Assign (x, e)  -> expr e @ [ST x]
  | Stmt.Skip           -> []
  | Stmt.If (e, s1, s2) -> let fLabel = env#next_label in
                let eLabel = env#next_label in
                expr e @ [CJMP ("z", fLabel)] @ 
                compile' env s1 @ [JMP eLabel; LABEL fLabel] @ 
                compile' env s2 @ [LABEL eLabel]
  | Stmt.While (e, s)   -> let loopLabel = env#next_label in
                let endLabel  = env#next_label in
                [LABEL loopLabel] @ expr e @ [CJMP ("z", endLabel)] @
                compile' env s @ [JMP loopLabel; LABEL endLabel]
  | Stmt.Repeat (e, s)  -> let startLabel = env#next_label in
                [LABEL startLabel] @ compile' env s @ expr e @ [CJMP ("z", startLabel)]

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile = compile' (new env)
