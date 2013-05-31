(* ?? *)
type solve_tactic_t = Cases

(* tactics to generate support= *)
type support_tactic_t = Full | Reduce | Reduce2

(* tactics to simplify formulas *)
type formula_tactic_t = SplitConsequent | SimplifyPC | PropositionalPropagate

type support_info
type verification_condition

type proof_plan

val support_tactic_from_string : string -> support_tactic
val formula_tactic_from_string : string -> formula_tactic


(* Get functions for type proof_plan *)
val get_cutoff       : proof_plan -> Smp.cutoff_strategy_t option
val get_solve        : proof_plan -> solve_tactic_t option
val get_support_tactics  : proof_plan -> pre_tac_t  list
val get_formula_tactics : proof_plan -> post_tac_t list

(* Get functions for type verification_conditions *)
val get_antecedent : verification_condition -> Expression.formula
val get_consequent_with_primes : verification_condition -> Expression.formula
val get_consequent_no_primes : verification_condition -> Expression.formula
val get_support : verification_condition -> Expression.formula list 
val get_tid_constraint : verification_condition -> Expression.formula 
val get_suport_vocabulary : verification_condition -> Expression.tid list 
val get_support_fresh_tid : verification_condition -> Expression.tid 
val get_rho : verification_condition -> Expression.tid 
val get_goal : verification_condition -> Expression.tid 
val get_transition_tid : verification_condition -> Expression.tid 
val get_line : verification_condition -> Expression.tid 
val get_vocabulary : verification_condition -> Expression.tid 



val specialize_tacs : t -> t -> t

val simplify : Expression.formula -> Expression.formula

val simplify_with_pc : Expression.formula -> 
                       Expression.tid -> 
                       int list ->
                       bool -> 
                       Expression.formula

val simplify_with_vocabulary : Expression.formula -> 
                               Expression.variable list -> 
                               Expression.formula

val generate_support : Expression.formula list ->
                       Expression.tid list ->
                       support_tactic_t list ->
                       support_info_t


val create_proof_plan : Smp.cutoff_strategy_t option ->
                        solve_tactic option ->
                        suport_tactic list ->
                        formula_tactic list ->
                        prood_plan

(* Get functions for proof plans *)
val get_smp_cutoff       : proof_plan -> Smp.cutoff_strategy_t option
val get_solve_tactic     : proof_plan -> solve_tactic option
val get_support_tactics  : proof_plan -> support_tacic list
val get_formula_tactics  : proof_plan -> formula_tacic list

(* TACTIC APPLICATION     *)

(* PROOF PLAN APPLICATION *)


