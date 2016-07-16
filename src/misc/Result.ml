
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


module E = Expression


type status_t =
  Unverified      |   (* The formula has not been analyzed              *)
  Invalid         |   (* The formula is invalid                         *)
  Valid of DP.t       (* The formula is valid                           *)


type info_t =
  {
    status : status_t;
    time : float;
  }


(******************)
(*  CONSTRUCTORS  *)
(******************)

let new_info (status:status_t) (time:float) : info_t =
  {
    status = status;
    time = time;
  }


let status_to_str (st:status_t) : string =
  match st with
  | Unverified -> "Unverified"
  | Invalid    -> "Invalid"
  | Valid dp   -> "Valid (" ^DP.to_str dp^ ")"


let get_status (info:info_t) : status_t =
  info.status


let get_time (info:info_t) : float =
  info.time


let is_unverified (info:info_t) : bool =
  info.status = Unverified


let is_invalid (info:info_t) : bool =
  info.status = Invalid


let is_valid (info:info_t) : bool =
  match info.status with
  | Valid _ -> true
  | _       -> false



