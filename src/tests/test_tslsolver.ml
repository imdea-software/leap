
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


let filename = ref ""

let _ =
  Arg.parse [] (fun str -> filename := str) "";

  if !filename = "" then
    print_endline "No input file provided."
  else begin
    let cfg = SMTExecute.new_configuration SMTExecute.Z3 in
    SMTExecute.compute_model cfg true;
    let result = SMTExecute.run cfg (LeapFile.read !filename) in
(*    let model = SMTExecute.get_model() in *)
    print_endline ("ANSWER: " ^ (if Sat.is_sat result then "SAT" else "UNSAT"))
  end
