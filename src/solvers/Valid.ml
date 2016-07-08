
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

(** Declares all possibilities answers from the SMT solver *)
type t =
  | Valid
  | Invalid
  | Unknown


let to_str (answer:t) : string =
  match answer with
  | Valid   -> "VALID"
  | Invalid -> "INVALID"
  | Unknown -> "UNKNOWN"


let from_str (str:string) : t =
  match (String.uppercase str) with
  | "VALID"   -> Valid
  | "INVALID" -> Invalid
  | "UNKNOWN" -> Unknown
  | _         -> raise(Unknown_answer_str str)


let is_valid (answer:t) : bool =
  answer == Valid


let is_invalid (answer:t) : bool =
  answer == Invalid


let is_unknown (answer:t) : bool =
  answer == Unknown

