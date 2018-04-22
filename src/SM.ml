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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' -> 
    match insn with
      | JMP s          -> eval env conf (env#labeled s)
        | CJMP (f, s)    -> let x::stack' = stack in 
                        let predicate = match f with
                           | "z"  -> (==) 0
                         | "nz" -> (!=) 0
                        in
                        if predicate x then eval env (cstack, stack', c) (env#labeled s) else eval env (cstack, stack', c) prg'
            | CALL (f, _, _) -> eval env ((prg', st)::cstack, stack, c) (env#labeled f)
            | END | RET _    -> (match cstack with
                                    | (p, st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) p
                                    | [] -> conf)
          | _ -> eval env
         (match insn with
          | BINOP op        -> let y::x::stack' = stack in (cstack, Expr.to_func op x y :: stack', c)
          | READ            -> let z::i'        = i     in (cstack, z::stack, (st, i', o))
          | WRITE           -> let z::stack'    = stack in (cstack, stack', (st, i, o @ [z]))
          | CONST i         -> (cstack, i::stack, c)
          | LD x            -> (cstack, State.eval st x :: stack, c)
          | ST x            -> let z::stack'    = stack in (cstack, stack', (State.update x z st, i, o))
          | LABEL s         -> conf
          | BEGIN (_, p, l) -> let enter_st = State.enter st (p @ l) in
                               let (st', stack') = List.fold_right (
                                   fun p (st, x::stack') -> (State.update p x st, stack')  
                                   ) p (enter_st, stack) in
                               (cstack, stack', (st', i, o))
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class env =
  object (self)
    val mutable label = 0
    method next_label = let last_label = label in
      label <- label + 1; Printf.sprintf "L%d" last_label
  end

let rec compile' env p =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, params) -> List.concat (List.map expr params) @ [CALL (f, List.length params, false)]
  in
  match p with
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
  | Stmt.Repeat (s, e)  -> let startLabel = env#next_label in
                 [LABEL startLabel] @ compile' env s @ expr e @ [CJMP ("z", startLabel)]
  | Stmt.Call (f, p)    -> List.concat (List.map expr p) @ [CALL (f, List.length p, true)]
  | Stmt.Return r       -> (match r with | None -> [RET false] | Some v -> expr v @ [RET true])

let compile_procedure env (name, (params, locals, body)) =
    [LABEL name; BEGIN (name, params, locals)] @ compile' env body @ [END] 

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = let env = new env in
    compile' env p @ [END] @ List.concat (List.map (compile_procedure env) defs)