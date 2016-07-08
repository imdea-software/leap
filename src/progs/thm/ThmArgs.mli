
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
(* @file ThmArgs.mli                                                          *)
(* Command Line Arguments for Thm                                             *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val debugFlag : bool ref
val use_z3 : bool ref
val use_q : bool ref
val coType : Smp.cutoff_strategy_t ref
val hide_pres : bool ref
val phiFile : string ref
val assignopt : 'a ref -> bool ref -> 'a -> unit
val setdebug : unit -> unit
val inputFormula : string -> unit
val co_opt_list : string list
val set_co : string -> unit
val assigninputfile : string -> unit
val opts : (string * Arg.spec * string) list
val anon_fun : string -> unit
val usagemsg : string
val error : Arg.usage_msg -> 'a
val simple_error : string -> 'a
val postcheck : unit -> unit
val parse_args : 'a -> unit
val open_input : 'a -> in_channel
val close_input : 'a -> unit
val arrangement_gen : bool ref
