type polarity = Pos | Neg | Both
type support_t = Expression.formula list
type vc_info
type verification_condition
type implication = {
  ante : Expression.formula ;
  conseq : Expression.formula ;
}

type support_split_tactic = SplitGoal
type support_tactic = Full | Reduce | Reduce2
type formula_tactic = SimplifyPC | PropositionalPropagate | FilterStrict
type formula_split_tactic = SplitConsequent
type solve_tactic = Cases

type support_split_tactic_t = vc_info -> vc_info list
type support_tactic_t = vc_info -> support_t
type formula_split_tactic_t = implication -> implication list
type formula_tactic_t = implication -> implication

type proof_plan =
  {
    cutoff_algorithm : Smp.cutoff_strategy_t option     ;
    solve            : solve_tactic option              ;
    support_split_tactics : support_split_tactic_t list ;
    support_tactics  : support_tactic list              ;
    formula_split_tactics : formula_split_tactic_t list ;
    formula_tactics  : formula_tactic list              ;
  }



val vc_info_to_implication : vc_info -> support_t -> implication



(***********************)
(* CONSTRUCTORS        *)
(***********************)

val new_proof_plan : Smp.cutoff_strategy_t option ->
                     solve_tactic option ->
                     support_split_tactic_t list ->
                     support_tactic list ->
                     formula_split_tactic_t list ->
                     formula_tactic list ->
                     proof_plan
val vc_info_to_formula : vc_info -> support_t -> Expression.formula
val vc_info_to_vc : vc_info -> support_t -> verification_condition
val default_cutoff_algorithm : Smp.cutoff_strategy_t
val support_tactic_from_string : string ->  support_tactic
val support_split_tactic_from_string : string ->  support_split_tactic
val formula_tactic_from_string : string ->  formula_tactic
val formula_split_tactic_from_string : string -> formula_split_tactic

val formula_tactic_to_string :formula_tactic -> string
val vc_info_to_str : vc_info -> string

val create_vc_info  : support_t ->
                      Expression.formula ->
                      Expression.formula ->
                      Expression.formula ->
                      Expression.tid list ->
                      Expression.tid ->
                      Expression.pc_t ->
                      vc_info 

val create_vc  : support_t -> 
               Expression.formula -> 
               Expression.formula -> 
               Expression.formula -> 
               Expression.tid list -> 
               Expression.tid -> 
               Expression.pc_t ->  
         support_t -> 
         verification_condition 

val dup_vc_info_with_goal : vc_info ->  Expression.formula ->   vc_info 

(****************************)
(* SELECTORS                *)
(****************************)
val get_cutoff : proof_plan ->   Smp.cutoff_strategy_t option 
val get_solve : proof_plan ->    solve_tactic option 
val get_support_tactics : proof_plan ->   support_tactic list 
val get_formula_tactics : proof_plan ->   formula_tactic list 
val get_unprocessed_support_from_info : vc_info ->   support_t 
val get_tid_constraint_from_info : vc_info ->   Expression.formula  
val get_vocabulary_from_info : vc_info ->   Expression.tid list      
val get_rho_from_info : vc_info ->   Expression.formula   
val get_goal_from_info : vc_info ->   Expression.formula   
val get_transition_tid_from_info : vc_info ->   Expression.tid   
val get_line_from_info : vc_info ->   Expression.pc_t   
val get_antecedent : verification_condition ->   Expression.formula
val get_consequent : verification_condition ->   Expression.formula
val get_support : verification_condition ->   support_t 
val get_unprocessed_support : verification_condition ->   support_t 
val get_tid_constraint : verification_condition ->   Expression.formula 
val get_rho : verification_condition ->   Expression.formula 
val get_goal : verification_condition ->   Expression.formula 
val get_transition_tid : verification_condition ->   Expression.tid 
val get_line : verification_condition ->   Expression.pc_t 
val get_vocabulary : verification_condition ->   Expression.tid list 


(***************)
(* SIMPLIFIERS *)
(***************)
val generic_simplifier : Expression.formula ->  
      (Expression.literal-> polarity->Expression.formula) ->   Expression.formula 

val simplify : Expression.formula ->   Expression.formula 
val simplify_with_pc : Expression.formula ->  Expression.tid ->  int list ->  bool ->   Expression.formula 
val simplify_with_vocabulary : Expression.formula ->  Expression.variable list ->  Expression.formula 
val generate_support : vc_info ->   Expression.formula list 
val split_implication : implication ->   implication list
val split_goal :vc_info -> vc_info list

val tactic_propositional_propagate : implication -> implication 

val filter_with_variables_in_conseq : implication -> implication


(**************************************************************************)
(* CONVERTERS: From tactic names to tactics functions                     *)
(**************************************************************************)

val pick_support_split_tac : support_split_tactic -> support_split_tactic_t
val pick_support_tac : support_tactic -> support_tactic_t
val pick_formula_split_tac : formula_split_tactic -> formula_split_tactic_t
val pick_formula_tac : formula_tactic -> formula_tactic_t


(**************************************************************************)
(* APPLICATION OF TACTICS                                                 *)
(**************************************************************************)

val apply_support_split_tactics : vc_info list -> support_split_tactic list -> vc_info list
val apply_support_tactic : vc_info list -> support_tactic option -> implication list
val apply_formula_split_tactics : implication list -> formula_split_tactic list -> implication list
val apply_formula_tactics : implication list -> formula_tactic list -> implication list
val apply_tactics : vc_info list ->
                    support_split_tactic list ->
                    support_tactic option ->
                    formula_split_tactic list ->
                    formula_tactic list ->
                    Expression.formula list
