module type CUSTOM_NUMSOLVER = sig
  module Exp    : ExpressionTypes.EXPRESSION
  module NumExp : ExpressionTypes.NUMEXP
  
  (* Basic invocations *)
  val check_sat              : NumExp.formula -> Sat.t
  val check_valid            : NumExp.formula -> Valid.t
  
  
  (* Invocations with extra information *)
  val check_valid_plus_info  : NumExp.formula -> (Valid.t * int)
  
  val check_sat_with_lines   : int -> NumExp.formula -> Sat.t
  val check_valid_with_lines : int -> NumExp.formula -> Valid.t
  
  val check_valid_with_lines_plus_info 
                          : int -> NumExp.formula -> (Valid.t * int)

 
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


  (* Counter models management *)
  val compute_model : bool -> unit
  val model_to_str  : unit -> string
  val print_model   : unit -> unit
  val get_sort_map  : unit -> GenericModel.sort_map_t
  val get_model     : unit -> GenericModel.t
  
end

module type S = CUSTOM_NUMSOLVER
  with module Exp = Expression
  and  module NumExp = NumExpression

module Make : functor (Solver : BackendSolverIntf.BACKEND_NUM) -> S

val choose : string -> (module S)

val try_sat : Expression.formula -> Sat.t
