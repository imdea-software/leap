
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


type node_id_t = string
type box_id_t = string
type edge_type_t = Any | Pres
type trans_t = NoLabel | Label of (int * Expression.V.t) list
type edge_info_t = (edge_type_t * trans_t)
type accept_triple_t = (node_id_t * node_id_t * edge_type_t)
type conditions_t = Initiation | Consecution | Acceptance | Fairness
type supp_line_t =
  | All
  | Trans of int
  | TransSpec of int * conditions_t
  | TransNodeSpec of int * node_id_t list * conditions_t list

module AcceptanceSet : Set.S with type elt = accept_triple_t

type wf_op_t =
  | WFIntSubset
  | WFPairSubset
  | WFAddrSubset
  | WFElemSubset
  | WFTidSubset
  | WFIntLess

type acceptance_t = {good : AcceptanceSet.t;
                     bad  : AcceptanceSet.t;
                     delta: (Expression.term * wf_op_t) list; }

module NodeIdSet : Set.S with type elt = node_id_t
module EdgeInfoSet : Set.S with type elt = edge_info_t

type t
type support_t

exception Unknown_condition_str of string

val new_pvd : string ->
              (node_id_t * Expression.formula) list ->
              (box_id_t * node_id_t list * Expression.ThreadSet.elt) list ->
              (node_id_t list) ->
              (node_id_t * node_id_t * (edge_type_t * trans_t)) list ->
              (accept_triple_t list * accept_triple_t list * (Expression.term * wf_op_t) list) list ->
              t

val def_cond_list : conditions_t list

val initial : t -> NodeIdSet.t
val nodes : t -> NodeIdSet.t
val node_mu : t -> node_id_t -> Expression.formula
val node_box : t -> node_id_t -> box_id_t option
val next : t -> node_id_t -> NodeIdSet.t
val cond_next : t -> edge_type_t -> node_id_t -> NodeIdSet.t
val box_param : t -> box_id_t -> Expression.ThreadSet.elt
val edges : t -> node_id_t -> node_id_t -> EdgeInfoSet.t
val edge_list : t -> (node_id_t * node_id_t * EdgeInfoSet.t) list
val successor : t -> node_id_t -> int -> Expression.V.t -> NodeIdSet.t
val acceptance_list : t -> acceptance_t list
val beta : t -> (node_id_t * node_id_t * edge_type_t) -> Expression.formula
val ranking_function : Expression.formula ->
                       acceptance_t ->
                       (node_id_t * node_id_t * edge_type_t) ->
                       Expression.formula
val free_voc : t -> Expression.ThreadSet.t


val new_support : (supp_line_t * Tactics.proof_plan) list ->
                  (supp_line_t * Tag.f_tag list) list ->
                  support_t

val supp_tags : support_t -> Tag.f_tag list
val supp_fact : support_t -> int -> node_id_t option -> conditions_t -> Tag.f_tag list
val supp_plan : support_t -> int -> node_id_t option -> conditions_t -> Tactics.proof_plan

val to_str : t -> string
val cond_to_str : conditions_t -> string
val str_to_cond : string -> conditions_t
