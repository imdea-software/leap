type iGraph_t

type premise_t = Normal | Extra

type mode_t = Sequential | Concurrent

type rule_t

val empty_igraph : unit -> iGraph_t
val new_igraph : rule_t list -> iGraph_t
val add_rule : iGraph_t -> rule_t -> iGraph_t
val new_rule :
  mode_t ->
  Tag.f_tag list ->
  Tag.f_tag ->
  (Expression.pc_t * premise_t list * Tag.f_tag list * Tactics.proof_plan) list ->
  Tactics.proof_plan -> rule_t


val graph_info :
      iGraph_t ->
        (mode_t *
         Tag.f_tag list *
         Tag.f_tag *
         (Expression.pc_t * premise_t, Tag.f_tag list * Tactics.proof_plan) Hashtbl.t *
         Tactics.proof_plan) list

val graph_tags : iGraph_t -> Tag.f_tag list
