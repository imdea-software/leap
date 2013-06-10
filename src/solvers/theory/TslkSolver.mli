module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TSLKEXP
 
  
  val is_sat_conj  : int -> TslkExp.conjunctive_formula -> bool
  val is_sat_dnf   : int -> TslkExp.formula -> bool
  
  val is_valid_dnf : int -> TslkExp.formula -> bool
  val is_valid_dnf_pus_info
                   : int -> TslkExp.formula -> (bool * int)
    
  val is_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     TslkExp.formula -> bool
  val is_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     TslkExp.formula -> bool
  
  val is_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     TslkExp.formula -> (bool * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model : unit -> GenericModel.t

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TSLKSOLVER


module Make (K : Level.S)
            (Solver : BackendSolverIntf.BACKEND_TSLK) : S

val choose : string -> int -> (module S)
