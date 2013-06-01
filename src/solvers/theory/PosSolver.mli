module type CUSTOM_POSSOLVER = sig
  module PosExp : ExpressionTypes.POSEXP
  
  val is_sat   : int -> PosExp.expression -> bool
  val is_valid : int -> PosExp.expression -> bool
end

module type S = CUSTOM_POSSOLVER
  with module PosExp = PosExpression

module Make : functor (Solver : BackendSolverIntf.BACKEND_POS) -> S

val choose : string -> (module S)
