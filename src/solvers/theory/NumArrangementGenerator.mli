
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



(** The type of a numeric arrangement generator *)
type t

(** [new_arr_gen arr] returns a new numeric arrangement generator, using the
 * information contained in [arr] to set the initial restrictions of
 * future generated arrangements. *)
val new_arr_gen : NumExpression.integer Arrangements.t -> t

(** [next_arr ag] generates a new valid numeric arrangement and returns it. If no
 * further valid arrangements exists, then it return the empty lists. *)
val next_arr : t -> NumExpression.integer list list

