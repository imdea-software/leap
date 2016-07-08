
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

type axiom_kind_t = Forall | Instantiate
type rule_t
type case_t
type case_tbl_t
type axiom_tbl_t

val empty_axioms : unit -> t
val new_axioms : rule_t list -> t
val new_axiom_table : Tag.tag_table -> axiom_tbl_t
val new_rule : Tag.f_tag -> case_t list -> rule_t
val new_case : Expression.pc_t -> (Tag.f_tag * axiom_kind_t) list -> case_t

val axiom_table_to_str : axiom_tbl_t -> string

val lookup : t -> Tag.f_tag -> Expression.pc_t -> (Tag.f_tag * axiom_kind_t) list

val apply : axiom_tbl_t -> Expression.formula -> Tag.f_tag -> axiom_kind_t ->
            (Expression.formula * Expression.formula)

