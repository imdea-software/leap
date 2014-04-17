type node_id_t = string
type box_id_t = string
type supp_line_t = All | Trans of int
type edge_type_t = Any | Pres
type trans_t = NoLabel | Label of (int * Expression.V.t) list
type accept_triple_t = (node_id_t * node_id_t * edge_type_t)

module NodeIdSet : Set.S with type elt = node_id_t

type t
type support_t

val new_pvd : string ->
              (node_id_t * Expression.formula) list ->
              (box_id_t * node_id_t list * Expression.ThreadSet.elt) list ->
              (node_id_t list) ->
              (node_id_t * node_id_t * (edge_type_t * trans_t)) list ->
              (accept_triple_t list * accept_triple_t list * Expression.formula) 
              list ->
              t

val initial : t -> NodeIdSet.t
val node_mu : t -> node_id_t -> Expression.formula
val node_box : t -> node_id_t -> box_id_t option


val new_support : (supp_line_t * Tactics.proof_plan) list ->
                  (supp_line_t * Tag.f_tag list) list ->
                  support_t

val supp_tags : support_t -> Tag.f_tag list
val supp_fact : support_t -> int -> Tag.f_tag list
val supp_plan : support_t -> int -> Tactics.proof_plan

val to_str : t -> string

