
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



exception Unknown_strategy_str of string

type cutoff_strategy_t =
  | Dnf       (* Computes dnf over the formula and then counts literals *)
  | Union     (* Computes an upper bound using union over literals *)
  | Pruning   (* Computes a better bound, by pruning non interesting literals *)


type cutoff_options_t

val def_strategy_list : cutoff_strategy_t list

val strategy_to_str : cutoff_strategy_t -> string

val str_to_strategy : string -> cutoff_strategy_t


val opt_empty : unit -> cutoff_options_t

val set_forget_primed_mem : cutoff_options_t -> bool -> unit

val set_group_vars : cutoff_options_t -> bool -> unit

val forget_primed_mem : cutoff_options_t -> bool

val group_vars : cutoff_options_t -> bool
