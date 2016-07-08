
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



(** [set_logFile filename] configures [filename] to be the log file. *)
val set_logFile : string -> unit

(** [get_logFile ()] returns the name of the current log file *)
val get_logFile : unit -> string

(** [print label str] prints [str] to the current log file using [label]
    to label the entry. *)
val print : string -> string -> unit

(** [print_ocaml str] prints [str] into the current log file using "ocaml"
    as label *)
val print_ocaml : string -> unit

(** [print_cfg str] prints [str] into the current log file using "prog 
    configuration" as label *)
val print_cfg : string -> unit
