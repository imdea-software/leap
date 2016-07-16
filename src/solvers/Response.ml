
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



let sat_to_valid (answer:Sat.t) : Valid.t =
  match answer with
  | Sat.Sat     -> Valid.Invalid
  | Sat.Unsat   -> Valid.Valid
  | Sat.Unknown -> Valid.Unknown


let valid_to_sat (answer:Valid.t) : Sat.t =
  match answer with
  | Valid.Valid   -> Sat.Unsat
  | Valid.Invalid -> Sat.Sat
  | Valid.Unknown -> Sat.Unknown
