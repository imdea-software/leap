
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


let logFile : string ref = ref ""

let out : Pervasives.out_channel ref = ref Pervasives.stdout


let set_logFile (fileName:string) : unit =
  if fileName <> "" then begin
    logFile := fileName;
    out := Pervasives.open_out fileName
  end


let get_logFile () : string =
  !logFile


let is_set () : bool =
  !logFile <> ""


let close () : unit =
  if is_set() then Pervasives.close_out !out


let print (label:string) (str:string) : unit =
  if is_set() then begin
    let label_str = match label with
                    | "" -> ""
                    | _  -> "**" ^ label ^ ": " in
    Pervasives.output_string !out (label_str ^ str ^ "\n");
    Pervasives.flush !out
  end


let print_ocaml (str:string) : unit =
  print "ocaml" str


let print_cfg (str:string) : unit =
  print "prog configuration" str
