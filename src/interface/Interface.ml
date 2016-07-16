
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


(* Interface.ml *)


module File =
struct
  let readFile (fileName:string) : string =
    let ic = open_in fileName in
    let n = in_channel_length ic in
    let s = Bytes.create n in
      really_input ic s 0 n;
      close_in ic;
      (s)


  let writeFile (fileName:string) (str:string) : unit =
    let oc = open_out fileName in
    let _ = Printf.fprintf oc "%s" str in
      close_out oc


  let readChannel (ch:Pervasives.in_channel) : string =
    let result = ref "" in
    let rec read _ = try
                       let str = Pervasives.input_line ch in
                       let _ = result := !result ^ str ^ "\n"
                       in
                         read ()
                     with
                     | End_of_file -> Unix.close_process_in ch in
    let _ = read ()
    in
      !result
  

end


module Err =
struct

  let msg (title:string) (info:string) =
    Printf.eprintf "\n**** %s ****\n\n%s\n\n" title info


  let smsg (title:string) (info:string) =
    Printf.eprintf "**** %s: %s ****\n" title info

end


module Msg =
struct

  let div (title:string) : string =
    let size = String.length title in
    if size <= 70 then
      let rem = 78 - size in
      let lineA = String.make (rem/2) '-' in
      let lineB = String.make (rem - rem/2) '-' in
      lineA ^ " " ^ title ^ " " ^ lineB ^ "\n"
    else
      "---- " ^ title ^ " ----\n"


  let info (title:string) (info:string) : string =
    let border = div title in
      border ^ info ^ "\n" ^ border

end
