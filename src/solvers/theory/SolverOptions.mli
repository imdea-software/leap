
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


type t

(** The type of the theory solver options *)

val new_opt : unit -> t
(** [new_opt ()] generates a new theory solver option. By default, it sets
    number of program lines to 1, cut-off strategy to disjunctive normal
    form (DNF), use of quantifiers is disabled and the use of an
    arrangement generator is also disabled. *)
    
val set_lines : t -> int -> unit
(** [set_lines opt l] sets the number of program lines for options [opt]
    to [l]. *)

val set_cutoff_strategy : t -> Smp.cutoff_strategy_t -> unit
(** [set_cutoff_strategy opt co] sets [co] as the cut-off strategy for
    option [opt]. *)

val set_use_quantifiers : t -> bool -> unit
(** [set_use_quantifiers opt b] enables or disables the use of quantifiers
    for option [opt], according to parameter [b]. *)

val set_use_arrangement_generator : t -> bool -> unit
(** [set_use_arrangement_generator opt b] enables or disables the use of
    an arrangement generator for option [opt], according to parameter [b].
    *)

val lines : t -> int
(** [lines opt] returns the number of lines associated to the program
    being analyzed for the theory solver, according to option [opt]. *)

val cutoff_strategy : t -> Smp.cutoff_strategy_t
(** [cutoff_strategy opt] returns the cut-off strategy specified for this
    the theory solver option [opt]. *)

val use_quantifiers : t -> bool
(** [use_quantifier opt] indicates whether according to option [opt] the
    theory solver should use or not a translation for quantifiers over
    finite domains. *)

val use_arrangement_generator : t -> bool
(** [use_arrangement_generator opt] indicates whether according to option
    [opt] there should be used an SMT based arrangement generator for
    finding satisfiable arrangements between integers. *)
