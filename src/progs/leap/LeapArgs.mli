
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
(* @file LeapArgs.ml                                                          *)
(* Command Line Arguments for Leap                                            *)
(******************************************************************************)

exception MoreThanOneInputFile
exception No_file
exception No_inv_folder
exception Unknown_tag of string
exception InvalidRange of string

val input_file : string ref
val is_input_file : bool ref
val input_file_fd : Unix.file_descr ref
val showFlag : bool ref
val debugFlag : bool ref
val pinvSys : bool ref
val pinvPlusSys : bool ref
val useGraph : bool ref
val useAxioms : bool ref
val openExtSys : bool ref
val binvSys : bool ref
val spinvSys : bool ref
val vcgenFlag : bool ref
val vdFlag : bool ref
val pvdFlag : bool ref
val use_z3 : bool ref
val use_yices_plus_z3 : bool ref
val use_sat : bool ref
val expand_pres : bool ref
val count_abs : bool ref
val show_models : bool ref
val show_label_info : bool ref
val keep_primed_mem : bool ref
val group_vars : bool ref
val use_smt : bool ref
val arrangement_gen : bool ref
val dpType : DP.t ref
val coType : Smp.cutoff_strategy_t ref
val logFile : string ref
val invCandidate : string ref
val vdFormula : string ref
val supInvariant : string ref
val invFolder : string ref
val axiomFolder : string ref
val iGraphFile : string ref
val iAxiomFile : string ref
val focusPC : int list ref
val ignorePC : int list ref
val pvdConds : PVD.conditions_t list ref
val pvdNodes : PVD.node_id_t list ref
val vdFile : string ref
val pvdFile : string ref
val pvdSupport : string ref
val outFile : string ref
val detailedOutFile : string ref
val num_threads : int ref
val use_quantifiers : bool ref
val output_vcs : bool ref
val stop_on_invalid : bool ref

val assignopt : 'a ref -> bool ref -> 'a -> unit
val setdebug : unit -> unit
val inputInvFolder : string -> unit
val inputInvGraphFile : string -> unit
val inputInvariant : string -> unit
val inputFormula : string -> unit
val inputClosedSys : string -> unit
val inputVd : string -> unit
val inputPvd : string -> unit
val set_dp : string -> unit
val co_opt_list : string list
val set_co : string -> unit
val assigninputfile : string -> unit
val supportInvariant : string -> unit
val focusPos : string -> unit
val ignorePos : string -> unit
val opts : (string * Arg.spec * string) list
val anon_fun : string -> unit
val usagemsg : string
val error : Arg.usage_msg -> 'a
val simple_error : string -> 'a
val postcheck : unit -> unit
val parse_args : 'a -> unit
val open_input : 'a -> in_channel
val close_input : 'a -> unit
