
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


exception Undefined_tag of string
exception Duplicated_tag of string

type f_tag
type f_info
type tag_table

module TagSet : Set.S with type elt = f_tag

val new_tag     : string -> string -> f_tag
val new_info    : System.var_table_t -> f_info
val info_params : f_info -> System.var_table_t

val tag_id    : f_tag -> string
val master_id : f_tag -> string
val subtag_id : f_tag -> string


val tag_table_new         : unit -> tag_table
val tag_table_clear       : tag_table -> unit
val tag_table_add         : tag_table -> f_tag -> Expression.formula -> f_info -> unit
val tag_table_mem         : tag_table -> f_tag -> bool
val tag_table_find        : tag_table -> f_tag -> Expression.formula * f_info
val tag_table_get_formula : tag_table -> f_tag -> Expression.formula
val tag_table_get_info    : tag_table -> f_tag -> f_info
val tag_table_size        : tag_table -> int
val tag_table_iter        : tag_table -> (f_tag -> (Expression.formula * f_info) -> unit) -> unit
