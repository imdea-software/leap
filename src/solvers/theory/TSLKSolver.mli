module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TLLEXP
  
  module Smp : sig
    type cutoff_strategy
  end
  
  val is_sat_conj  : int -> TllExp.conjunctive_formula -> bool
  val is_sat_dnf   : int -> TllExp.formula -> bool
  
  val is_valid_dnf : int -> TllExp.formula -> bool
  val is_valid_dnf_pus_info 
                   : int -> TllExp.formula -> (bool * int)
    
  val is_sat       : int ->
                     Tactics.solve_tactic_t option ->
                     Smp.cutoff_strategy ->
                     TllExp.formula -> bool
  val is_valid     : int ->
                     Tactics.solve_tactic_t option ->
                     Smp.cutoff_strategy ->
                     TllExp.formula -> bool
  
  val is_valid_plus_info 
                   : int ->
                     Tactics.solve_tactic_t option ->
                     Smp.cutoff_strategy ->
                     TllExp.formula -> (bool * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TLLSOLVER
  with module TllExp = TllExpression
  and  module Smp = SmpTll
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_TLL) -> S

val choose : string -> (module S)
