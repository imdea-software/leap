type iGraph_t

type premise_t = Normal | Extra

type rule_t

val empty_igraph : unit -> iGraph_t
val new_igraph : rule_t list -> iGraph_t
val add_rule : iGraph_t -> rule_t -> iGraph_t
val new_rule :
  Tag.f_tag list ->
  Tag.f_tag ->
  (Expression.pc_t * premise_t list * Tag.f_tag list * Tactics.t) list ->
  Tactics.t -> rule_t

val graph_info : iGraph_t 
  -> (Tag.f_tag list * Tag.f_tag * 
      (Expression.pc_t * premise_t, Tag.f_tag list * Tactics.t) 
      Hashtbl.t * Tactics.t) 
     list

val graph_tags : iGraph_t -> Tag.f_tag list
