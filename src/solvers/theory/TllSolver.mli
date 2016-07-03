module type CUSTOM_TLLSOLVER = sig
  module TllExp : ExpressionTypes.TLLEXP

  val check_sat_conj  : SolverOptions.t -> TllExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : SolverOptions.t -> TllExp.formula -> Sat.t
  
  val check_valid_dnf : SolverOptions.t -> TllExp.formula -> Valid.t
  val check_valid_dnf_pus_info : SolverOptions.t -> TllExp.formula -> (Valid.t * int)
    
  val check_sat : SolverOptions.t -> TllExp.formula -> Sat.t
  val check_valid : SolverOptions.t -> TllExp.formula -> Valid.t
  
  val check_valid_plus_info : SolverOptions.t -> TllExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model    : unit -> GenericModel.t

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TLLSOLVER
  with module TllExp = TllExpression
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_TLL) -> S

val choose : string -> (module S)
