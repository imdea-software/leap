
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


let _debug_ : bool ref = ref false
let _debug_level_ : int ref = ref 0
let _debug_show_tmpfile_info_ : bool ref = ref false
let _debug_show_problems_ : bool ref = ref false
let _debug_show_invTables_ : bool ref = ref false
let _debug_show_widening_formula_ : bool ref = ref false
let _debug_show_smt_ : bool ref = ref false
let _debug_force_assertions_ : bool ref = ref false


let infoLevel = 100

let msg (f:unit -> string) (level:int) : unit =
  if !_debug_ && !_debug_level_ >= level then
    print_endline (f ())


let infoMsg (f:unit -> string) : unit =
  msg f infoLevel


let print_file_name (label:string) (file_name:string) : unit =
  if !_debug_show_tmpfile_info_ then
    let out_str = Printf.sprintf "%s information in file %s" label file_name
    in
      print_endline out_str


let force_print_file_name (label:string) (file_name:string) : unit =
  let out_str = Printf.sprintf "%s information in file %s" label file_name
  in
    print_endline out_str


let print_smt_result (sat:Sat.t) : unit =
  if !_debug_show_tmpfile_info_ then
    print_endline ("[" ^ Sat.to_str sat ^ "]")


let print_trsProblem (prob_str:string) : unit =
  if !_debug_show_problems_ then
    let out_str = Printf.sprintf
                    "+---- Output from trsParse -----------------------------\n\
                     %s\n\
                     +-------------------------------------------------------"
                      prob_str
    in
      print_endline out_str


let print_invTables (pre_str:string) (post_str:string) : unit =
  if !_debug_show_invTables_ then
    let out_str = Printf.sprintf
                    "+---- After an iteration, previous invariants ----------\n\
                    %s\n\
                    +---- New calculated invariants -------------------------\n\
                    %s\n\
                    +--------------------------------------------------------"
                      pre_str post_str
    in
      print_endline out_str


let print_widening_formulas (loc:int list)
                            (f1:string)
                            (f2:string)
                            (w:string) : unit =
  if !_debug_show_widening_formula_ then
    let loc_str = String.concat "_" (List.map string_of_int loc) in
    let out_str = Printf.sprintf
                    "+---- Widening info for location %s begins -------------\n\
                     Formula 1: %s\n\
                     Formula 2: %s\n\
                     Widening : %s\n\
                     +---- Widening info for location %s ends ---------------"
                      loc_str f1 f2 w loc_str
    in
      print_endline out_str


let  print_smt (msg:string) : unit =
  if !_debug_show_smt_ then
    print_endline msg


let  print_smt_query (q:string) : unit =
  if !_debug_show_smt_ then
   print_endline (Printf.sprintf "Query:\n%s" q)
