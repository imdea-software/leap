
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)


type polarity = Pos | Neg | Both
type assumption_t = ModelFunc of Expression.tid * Expression.tid
type support_t = Expression.formula list
type tid_constraints_t
type vc_info
type verification_condition
type implication = {
  ante : Expression.formula ;
  conseq : Expression.formula ;
}

type support_option_t =
  | DefaultSupport 
  | FilterSupport

type support_split_tactic_t = vc_info -> vc_info list
type support_tactic_t = (vc_info -> support_t) * support_option_t
type formula_split_tactic_t = implication -> implication list
type formula_tactic_t = implication -> implication

type proof_plan =
  {
    cutoff_algorithm : Smp.cutoff_strategy_t option     ;
    support_split_tactics : support_split_tactic_t list ;
    support_tactics  : support_tactic_t list            ;
    formula_split_tactics : formula_split_tactic_t list ;
    formula_tactics  : formula_tactic_t list            ;
  }



val vc_info_to_implication : vc_info -> support_t -> implication



(***********************)
(* CONSTRUCTORS        *)
(***********************)

val new_tid_constraint : (Expression.tid * Expression.tid) list ->
                         (Expression.tid * Expression.tid) list -> tid_constraints_t

val new_proof_plan : Smp.cutoff_strategy_t option ->
                     support_split_tactic_t list ->
                     support_tactic_t list ->
                     formula_split_tactic_t list ->
                     formula_tactic_t list ->
                     proof_plan
val vc_info_to_formula : vc_info -> support_t -> Expression.formula
val vc_info_to_vc : vc_info -> support_t -> verification_condition
val default_cutoff_algorithm : Smp.cutoff_strategy_t
val support_tactic_from_string : string ->  support_tactic_t
val support_split_tactic_from_string : string ->  support_split_tactic_t
val formula_tactic_from_string : string ->  formula_tactic_t
val formula_split_tactic_from_string : string -> formula_split_tactic_t

val vc_info_to_str : vc_info -> string
val vc_info_to_plain_str : vc_info -> string
val vc_info_to_str_simple : vc_info -> string
val vc_info_list_to_folder : string -> vc_info list -> unit

val create_vc_info  : ?prime_goal:bool ->
                      ?tag:Tag.f_tag ->
                      support_t ->
                      tid_constraints_t ->
                      Expression.formula ->
                      Expression.formula ->
                      Expression.ThreadSet.t ->
                      Expression.tid ->
                      Expression.pc_t ->
                      vc_info

val to_plain_vc_info : Expression.fol_mode_t -> vc_info -> vc_info

val create_vc  : ?prime_goal:bool ->
                 ?tag:Tag.f_tag ->
                 support_t ->
                 tid_constraints_t ->
                 Expression.formula ->
                 Expression.formula ->
                 Expression.ThreadSet.t ->
                 Expression.tid ->
                 Expression.pc_t ->
                 support_t ->
                 verification_condition 

val dup_vc_info_with_goal : vc_info ->  Expression.formula ->   vc_info 

val add_modelfunc_assumption : vc_info -> assumption_t -> vc_info
val set_fixed_voc : Expression.ThreadSet.t -> unit
val vc_info_add_support : vc_info -> support_t -> vc_info

(****************************)
(* SELECTORS                *)
(****************************)
val get_cutoff : proof_plan ->   Smp.cutoff_strategy_t option
val get_support_tactics : proof_plan ->   support_tactic_t list
val get_formula_tactics : proof_plan ->   formula_tactic_t list
val empty_proof_plan : proof_plan
val is_empty_proof_plan : proof_plan -> bool
val get_unprocessed_support_from_info : vc_info ->   support_t
val get_tid_constraint_from_info : vc_info -> tid_constraints_t
val get_vocabulary_from_info : vc_info ->   Expression.ThreadSet.t
val get_rho_from_info : vc_info ->   Expression.formula
val get_goal_from_info : vc_info ->   Expression.formula
val get_transition_tid_from_info : vc_info ->   Expression.tid
val get_line_from_info : vc_info ->   Expression.pc_t
val get_original_vc_id : vc_info -> int
val get_vc_tag : vc_info -> Tag.f_tag
val get_antecedent : verification_condition ->   Expression.formula
val get_consequent : verification_condition ->   Expression.formula
val get_support : verification_condition ->   support_t
val get_unprocessed_support : verification_condition ->   support_t
val get_tid_constraint : verification_condition -> tid_constraints_t
val get_rho : verification_condition ->   Expression.formula
val get_goal : verification_condition ->   Expression.formula
val get_transition_tid : verification_condition ->   Expression.tid
val get_line : verification_condition ->   Expression.pc_t
val get_vocabulary : verification_condition ->   Expression.ThreadSet.t

val no_tid_constraint : tid_constraints_t
val is_empty_tid_constraint : tid_constraints_t -> bool

(**************************************************************************)
(* VARIABLE EQUALITY PROPAGATION                                          *)
(**************************************************************************)

val gen_eq_propagation : Expression.formula ->
                         (Expression.formula * Expression.V.subst_t)
val gen_eq_prop_from_list : Expression.formula list ->
                            (Expression.formula list * Expression.V.subst_t)

(**************************************************************************)
(* APPLICATION OF TACTICS                                                 *)
(**************************************************************************)

val apply_support_split_tactics : vc_info list -> support_split_tactic_t list -> vc_info list
val apply_support_tactic : vc_info list -> support_tactic_t option -> implication list
val apply_formula_split_tactics : implication list -> formula_split_tactic_t list -> implication list
val apply_formula_tactics : implication list -> formula_tactic_t list -> implication list
val apply_tactics : vc_info list ->
                    support_split_tactic_t list ->
                    support_tactic_t option ->
                    formula_split_tactic_t list ->
                    formula_tactic_t list ->
                    Expression.formula list
val apply_tactics_from_proof_plan : vc_info list -> proof_plan -> Expression.formula list
