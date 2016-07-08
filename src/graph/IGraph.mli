
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
