module type CUSTOM_POSSOLVER = sig
  module PosExp : ExpressionTypes.POSEXP
  
  val check_sat   : int -> PosExp.expression -> Sat.t
  val check_valid : int -> PosExp.expression -> Valid.t
end

module type S = CUSTOM_POSSOLVER
  with module PosExp = PosExpression

module Make : functor (Solver : BackendSolverIntf.BACKEND_POS) -> S

val choose : string -> (module S)
