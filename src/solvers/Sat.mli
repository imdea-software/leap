
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



exception Unknown_answer_str of string

(** Declares all possibilities answers from the SMT solver for
 * satisfiablity *)
type t =
  | Sat
  | Unsat
  | Unknown


val to_str : t -> string
(** [to_str r] returns a string representation of [r] *)

val from_str : string -> t
(** [from_str r] constructs an answer depending on the received string *)

val is_sat : t -> bool
(** [is_sat r] returns true if [r] represents a SAT answer *)

val is_unsat : t -> bool
(** [is_unsat r] returns true if [r] represents a UNSAT answer *)

val is_unknown : t -> bool
(** [is_unknown r] returns true if [r] represents a UNKNOWN answer *)
