
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



val reset_comment_sym : unit -> unit
(** [reset_comment_sym()] restores the symbol to identify the beginning of
    a line comment to "//" *)

val set_comment_sym : string -> unit
(** [set_comment_sym s] sets [s] as the identifier for the beginning of a
    line comment *)

val get_comment_sym : unit -> string
(** [get_comment_sym ()] returns the current identifier used to denote the
    beginning of a line comment *)

val parse : Pervasives.in_channel -> (Lexing.lexbuf -> 'a) -> 'a
(** [parse ch p] parses the content of channel [ch] using [p] *)

val open_and_parse : string -> (Lexing.lexbuf -> 'a) -> 'a
(** [open_and_parse s p] opens file [s] and parses its content using [p] *)
