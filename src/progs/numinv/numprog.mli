
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



type loc_t
type guard_t
type trans_rel_t
type num_assign_t
type num_trans_info_t
type num_trans_t
type num_location_t
type num_problem_t
type inv_table_t
type domain_t = Poly | Intvl | Oct | IntvlPoly | Eq
type tactic_t = Split | Focus
type absIntMode_t = Lazy | Interf | Eager | EagerPlus

(* NUMBER OF STEPS BEFORE WIDENING *)
val wait_for_widening : int ref
val trs_widening : int ref
val iterations : int ref
val widening_steps : int ref

(* CONSTRUCTION FUNTIONS *)
val new_loc : int list -> loc_t
val new_num_problem : string ->
                      bool ->
                      System.t ->
                      Expression.tid list ->
                      bool ->
                      tactic_t option ->
                      bool ->
                      absIntMode_t ->
                      num_problem_t


(* PRINTING FUNCTIONS *)
(*val num_assign_to_str : num_assign_t -> string*)
val num_trans_info_to_str : num_trans_info_t -> string
val num_location_to_str : num_location_t -> string
val num_problem_to_str : num_problem_t -> string
val inv_table_to_str : inv_table_t -> string
val invs_for_spec : inv_table_t -> string

val stat_info_str : System.t -> num_problem_t -> string

val num_integer_paren_to_str : Expression.integer -> string


(* NUMERIC PROGRAM MANIPULATION FUNCTIONS *)
val iterate : num_problem_t -> domain_t -> inv_table_t option
