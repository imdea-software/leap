
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


module Arr = Arrangements
module ArrGen = NumArrangementGenerator
module NE = NumExpression

let new_int (id:string) : NE.integer =
  NE.Var (NE.build_var id NE.Int false NE.V.Shared NE.V.GlobalScope)

let _ =
  let arr = Arr.empty true in

  Arr.clear arr;

  Arr.add_elem arr (new_int "A");
  Arr.add_elem arr (new_int "B");
  Arr.add_elem arr (new_int "C");
  Arr.add_elem arr (new_int "D");

  Arr.set_minimum arr (new_int "D");

  Arr.add_lesseq arr (new_int "C") (new_int "A");

  Arr.add_ineq arr (new_int "C") (new_int "D");

  Arr.add_less arr (new_int "A") (new_int "B");

  let ag = ArrGen.new_arr_gen arr in
  let next_arr = ref (ArrGen.next_arr ag) in
  while (!next_arr <> []) do
    let str = "[" ^ String.concat ";"
                (List.map (fun xs ->
                  "[" ^ (String.concat "," (List.map NE.integer_to_str xs)) ^ "]"
                 ) (!next_arr)) ^ "]" in
    print_endline str;
    next_arr := ArrGen.next_arr ag
  done;

