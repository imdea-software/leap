
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


open CommonQuery


module type PAIRS_QUERY =
sig

  include COMMON_QUERY

  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of program lines to [n]. *)

  val pairs_formula_to_str : PairsExpression.formula -> string
  (** Returns the string representation of a formula in the theory of
   *  pairs. *)

  val pairs_formula_with_lines_to_str : PairsExpression.formula -> string
  (** Returns the string representation of a formula in the theory of
   * pairs, taking into consideration the number of lines in the program. *)

  val get_sort_map : unit -> GenericModel.sort_map_t
  (** Gets the declared mapping from elements to sorts *)

end
