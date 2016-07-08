
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


val _debug_ : bool ref
val _debug_level_ : int ref
val _debug_show_tmpfile_info_ : bool ref
val _debug_show_problems_ : bool ref
val _debug_show_invTables_ : bool ref
val _debug_show_widening_formula_ : bool ref
val _debug_show_smt_ : bool ref
val _debug_force_assertions_ : bool ref


val msg : (unit -> string) -> int -> unit
val print_file_name : string -> string -> unit
val force_print_file_name : string -> string -> unit
val print_smt_result : Sat.t -> unit
val print_trsProblem : string -> unit
val print_invTables : string -> string -> unit
val print_widening_formulas : int list -> string -> string -> string -> unit
val print_smt : string -> unit
val print_smt_query : string -> unit

val infoMsg : (unit -> string) -> unit
