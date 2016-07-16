
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



let empty_str =
  "[                                                                      ]   0%"

let bar_width = 70
let pos1 = bar_width + 3
let pos2 = bar_width + 4
let pos3 = bar_width + 5

let max = ref 100
let curr_pos = ref 1
let step = ref (100/bar_width)
let next_step = ref (!step)

let str = ref (empty_str)


let init (m:int) : unit =
  let s = m/bar_width in
  str := empty_str;
  curr_pos := 1;
  max := m-1;
  step := s;
  ()


let current (n:int) : unit =
  if n = !max then begin
    Bytes.set (!str) bar_width '=';
    Bytes.set (!str) pos1 '1';
    Bytes.set (!str) pos2 '0';
    Bytes.set (!str) pos3 '0';
    print_endline !str
  end else begin
    let percent = ((n * 100) / (!max)) in
    if percent < 10 then begin
      Bytes.set (!str) pos3 (String.get (string_of_int percent) 0)
    end else begin
      let percent_str = string_of_int percent in
      Bytes.set (!str) pos2 (String.get percent_str 0);
      Bytes.set (!str) pos3 (String.get percent_str 1)
    end;
    if (n * bar_width) / (!max) >= !curr_pos then begin
      Bytes.set (!str) (!curr_pos) '=';
      incr curr_pos;
      print_string ((!str) ^ "\r");
      flush stdout
    end
  end

