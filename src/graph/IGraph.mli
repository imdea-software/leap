type t

type mode_t = Sequential | Concurrent

type rule_t

type case_tbl_t

val empty_igraph : unit -> t
val new_igraph : rule_t list -> t
val add_rule : t -> rule_t -> t
val new_rule :
  mode_t ->
  Tag.f_tag list ->
  Tag.f_tag ->
  (Expression.pc_t * Premise.t list * Tag.f_tag list * Tactics.proof_plan) list ->
  Tactics.proof_plan -> rule_t


val graph_info : t -> (mode_t * Tag.f_tag list * Tag.f_tag * case_tbl_t * Tactics.proof_plan) list

val graph_tags : t -> Tag.f_tag list

val empty_case_tbl : unit -> case_tbl_t

val num_of_cases : case_tbl_t -> int

val lookup_case : case_tbl_t ->
                  Expression.pc_t ->
                  Premise.t ->
                  (Tag.f_tag list * Tactics.proof_plan) option
