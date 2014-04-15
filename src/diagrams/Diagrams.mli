type node_id_t = string
type box_id_t = string
type edge_type_t = Any | Pres
type trans_t = NoLabel | Label of (int * Expression.V.t) list
type accept_triple_t = (node_id_t * node_id_t * edge_type_t)

type pvd_t

val new_pvd : string ->
              (node_id_t * Expression.formula) list ->
              (box_id_t * node_id_t list * Expression.ThreadSet.elt) list ->
              (node_id_t list) ->
              (node_id_t * node_id_t * (edge_type_t * trans_t)) list ->
              (accept_triple_t list * accept_triple_t list * Expression.formula) list ->
              pvd_t

val to_str : pvd_t -> string

