
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



exception Unknown_dp_str of string

(** Declares all possibilities of available decision procedures *)
type t =
  | NoDP
  | Loc
  | Num
  | Pairs
  | Tll
  | Tsl
  | Tslk of int
  | Thm

type call_tbl_t


val def_dp_list : t list
(** The list of default decision procedures available to the user *)


val to_str : t -> string
(** [to_str dp] returns a string representation of [dp] *)


val from_str : string -> t
(** [from_str s] parses [s] and returns the decision procedure it represents. It
    it cannot match any decision procedure, then [NoDP] is returned. *)


val get_tslk_param : t -> int
(** [get_tslk_param dp] returns the TSLK parameter, if [dp] is tslk. Otherwise,
    it returns 1. *)



val new_call_tbl : unit -> call_tbl_t
(** [new_call_tbl ()] returns a new table to count calls to each decision
    procedure *)


val clear_call_tbl : call_tbl_t -> unit
(** [clear_call_tbl tbl] erases all information regarding calls to decision
    procedures in table [tbl] *)


val copy_call_tbl : call_tbl_t -> call_tbl_t
(** [copy_call_tbl tbl] returns a copy of [tbl] *)


val add_dp_calls : ?vc_id:int -> call_tbl_t -> t -> int -> unit
(** [add_dp_calls tbl dp n vc] adds to table [tbl] the information that decision
    procedure [dp] has been called [n] times to solve verification condition
    with id [vc] *)


val combine_call_table : call_tbl_t -> call_tbl_t -> unit
(** [combine_call_table src dst] extracts the information in table [src]
    and adds it to [dst] *)


val call_tbl_to_list : call_tbl_t -> (t * int) list
(** [call_tbl_to_list tbl] returns the information stored in [tbl] as
    a list of pairs of decision procedures with the number of times each
    decision procedure was called *)


val call_tbl_solving_to_list : call_tbl_t -> (t * int) list
(** [call_tbl_solving_to_list tbl] returns a list containing the number of
    original verification conditions solved by each decision procedure. If
    more than one decision procedure was required, then the most powerful
    decision procedure is taking into consideration *)

