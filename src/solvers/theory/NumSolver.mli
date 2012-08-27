module type CUSTOM_NUMSOLVER = sig
  module Exp    : ExpressionTypes.EXPRESSION
  module NumExp : ExpressionTypes.NUMEXP
  
  (* Basic invocations *)
  val is_sat              : NumExp.formula -> bool
  val is_valid            : NumExp.formula -> bool
  
  
  (* Invocations with extra information *)
  val is_valid_plus_info  : NumExp.formula -> (bool * int)
  
  val is_sat_with_lines   : int -> NumExp.formula -> bool
  val is_valid_with_lines : int -> NumExp.formula -> bool
  
  val is_valid_with_lines_plus_info 
                          : int -> NumExp.formula -> (bool * int)
  
  
  (* Queries over numeric formulas *)
  val int_implies         : NumExp.formula -> NumExp.formula -> bool
  val int_equivalent      : NumExp.formula -> NumExp.formula -> bool
  val compare_int_formulas
                          : NumExp.formula -> NumExp.formula -> bool
  val compare_eq_int_formulas 
                          : NumExp.formula -> NumExp.formula -> bool
  
  
  (* Queries over formulas, with implicit conversion to numeric formulas *)
  val implies             : Exp.formula -> Exp.formula -> bool
  val equivalent          : Exp.formula -> Exp.formula -> bool
  val compare_formulas    : Exp.formula -> Exp.formula -> bool
  val compare_eq_formulas : Exp.formula -> Exp.formula -> bool
  
  
  (* Standard widening *)
  val standard_widening   : NumExp.formula -> NumExp.formula -> NumExp.formula
  
  val standard_widening_conj 
                          : NumExp.literal list -> NumExp.literal list 
                              -> NumExp.literal list
end

module type S = CUSTOM_NUMSOLVER
  with module Exp = Expression
  and  module NumExp = NumExpression

module Make : functor (Solver : BackendSolverIntf.BACKEND_NUM) -> S

val choose : string -> (module S)
