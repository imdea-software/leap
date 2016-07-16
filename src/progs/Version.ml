
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


let version_major = 0

let version_minor = 2

let revision = Revision.value

let _enable_ : bool ref = ref false

let show () : unit =
  if !_enable_ then
    let major_str = string_of_int version_major in
    let minor_str = string_of_int version_minor in
    let revision_str = string_of_int revision in
    print_endline ("LEAP version " ^major_str^ "." ^minor_str^ "." ^revision_str ^
                   " - Compiled on " ^ Revision.date ^ " at " ^ Revision.time)
  else
    ()
