
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
(* @file LeapDebug.ml                                                         *)
(* Provides functions for debugging.                                          *)
(*                                                                            *)
(******************************************************************************)


let debug_enabled = ref false

let enable_debug () = debug_enabled := true
let disable_debug () = debug_enabled := false
let flush () = if !debug_enabled then
  Pervasives.flush Pervasives.stderr

let debug (msg : ('a, Format.formatter, unit) format) : 'a  =
  if !debug_enabled then Format.eprintf msg
  else Format.ifprintf Format.err_formatter msg

let is_debug_enabled () : bool =
  !debug_enabled

let _testing_ : bool ref = ref false

let _testing_smp_ () : ModelSize.t =
  let ms = ModelSize.create () in
  ModelSize.set ms ModelSize.Addr 6;
  ModelSize.set ms ModelSize.Elem 3;
  ModelSize.set ms ModelSize.Tid 3;
  ms
