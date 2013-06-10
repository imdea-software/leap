module type CUSTOM_TLLSOLVER = sig
  module TllExp : ExpressionTypes.TLLEXP
  
  
  val is_sat_conj  : int -> TllExp.conjunctive_formula -> bool
  val is_sat_dnf   : int -> TllExp.formula -> bool
  
  val is_valid_dnf : int -> TllExp.formula -> bool
  val is_valid_dnf_pus_info 
                   : int -> TllExp.formula -> (bool * int)
    
  val is_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> bool
  val is_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> bool
  
  val is_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     TllExp.formula -> (bool * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TLLSOLVER
  with module TllExp = TllExpression
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_TLL) -> S

val choose : string -> (module S)
