module type CUSTOM_POSSOLVER = sig
  module PosExp : ExpressionTypes.POSEXP
  
  val is_sat   : int -> PosExp.expression -> bool
  val is_valid : int -> PosExp.expression -> bool
end

module type S = CUSTOM_POSSOLVER
  with module PosExp = PosExpression

module Make(Solver : BackendSolverIntf.BACKEND_POS) : S =
struct
  module PosExp = Solver.Translate.Pos.Exp
  
  (* INVOCATIONS *)
  let is_sat (lines : int) (expr : PosExp.expression) : bool =
(*    LOG "is_sat..." LEVEL TRACE; *)
    (Solver.Translate.Pos.set_prog_lines lines;
     Solver.sat (Solver.Translate.Pos.expression expr))
  
  let is_valid (lines : int) (expr : PosExp.expression) : bool =
(*    LOG "Entering is_valid..." LEVEL TRACE; *)
    not (is_sat lines (PosExpression.Not(expr)))
end

let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.posTbl solverIdent
    with Not_found -> BackendSolvers.defaultPos () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_POS) in
  (module Make(Sol) : S)
