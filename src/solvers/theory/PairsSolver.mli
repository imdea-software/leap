module type CUSTOM_PAIRSSOLVER = sig
  module PairsExp : ExpressionTypes.PAIRSEXP
    
  (* Basic invocations *)
  val check_sat              : PairsExp.formula -> Sat.t
  val check_valid            : PairsExp.formula -> Valid.t
  
  (* Invocations with extra information *)
  val check_valid_plus_info  : PairsExp.formula -> (Valid.t * int)
  
  val check_sat_with_lines   : int -> PairsExp.formula -> Sat.t
  val check_valid_with_lines : int -> PairsExp.formula -> Valid.t
  
  val check_valid_with_lines_plus_info 
                          : int -> PairsExp.formula -> (Valid.t * int)


  (* Counter models management *)
  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model    : unit -> GenericModel.t
end

module type S = CUSTOM_PAIRSSOLVER
  with module PairsExp = PairsExpression
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_PAIRS) -> S

val choose : string -> (module S)
