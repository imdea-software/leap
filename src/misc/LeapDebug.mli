
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


(******************************************************************************)
(* @file LeapDebug.mli                                                        *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)

val enable_debug : unit -> unit
val disable_debug : unit -> unit
val flush : unit -> unit

val debug : ('a, Format.formatter, unit) format -> 'a

val is_debug_enabled : unit -> bool

val _testing_ : bool ref
val _testing_smp_ : unit -> ModelSize.t
