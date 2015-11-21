module type CUSTOM_THMSOLVER = sig
  module ThmExp : ExpressionTypes.THMEXP
  
  
  val check_sat_conj  : int -> bool -> ThmExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : int -> bool -> ThmExp.formula -> Sat.t
  
  val check_valid_dnf : int -> bool -> ThmExp.formula -> Valid.t
  val check_valid_dnf_pus_info : int -> bool -> ThmExp.formula -> (Valid.t * int)
    
  val check_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> Sat.t
  val check_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> Valid.t
  
  val check_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     ThmExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_THMSOLVER
  with module ThmExp = ThmExpression
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_THM) -> S

val choose : string -> (module S)
