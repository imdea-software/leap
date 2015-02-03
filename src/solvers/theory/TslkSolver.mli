module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TSLKEXP
 
  
  val check_sat_conj  : int -> bool -> TslkExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : int -> bool -> TslkExp.formula -> Sat.t
  
  val check_valid_dnf : int -> bool -> TslkExp.formula -> Valid.t
  val check_valid_dnf_pus_info
                   : int -> bool -> TslkExp.formula -> (Valid.t * int)
    
  val check_sat       : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     TslkExp.formula -> Sat.t
  val check_valid     : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     TslkExp.formula -> Valid.t
  
  val check_valid_plus_info 
                   : int ->
                     Smp.cutoff_strategy_t ->
                     bool ->
                     TslkExp.formula -> (Valid.t * int)

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
