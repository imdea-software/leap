
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

(** Result module *)

(** Status of the verification of a formula or verification condition *)
type status_t =
  Unverified      |   (* The formula has not been analyzed              *)
  Invalid         |   (* The formula is invalid                         *)
  Valid of DP.t       (* The formula is valid                           *)


(** Information type regarding the result of a verification process *)
type info_t


(** [new_info st t] returns a new information storing the status [st] and
    execution time [t] *)
val new_info : status_t -> float -> info_t


(** [status_to_str st] returns a string representing status [st] *)
val status_to_str : status_t -> string


(** [get_status info] returns the solving status stored in [info] *)
val get_status : info_t -> status_t


(** [get_time info] returns the time stored in [info] *)
val get_time : info_t -> float


(** [is_unverified info] returns [true] if the information in [info]
    corresponds to an unverified VC. *)
val is_unverified : info_t -> bool


(** [is_invalid info] returns [true] if the information in [info]
    corresponds to an invalid VC. *)
val is_invalid : info_t -> bool


(** [is_valid info] returns [true] if the information in [info] says
    it is valid. *)
val is_valid : info_t -> bool
