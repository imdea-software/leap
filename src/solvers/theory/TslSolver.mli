
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



val choose : string -> unit
(** [choose s] selects [s] as the decision procedure implementation to be
    used. *)


val check_sat    : SolverOptions.t -> TSLExpression.formula -> Sat.t
(** [check_sat opt phi] checks the satisfiability of formula
    [phi], assuming the options states in [opt]. It returns [Sat] if the
    formula is satisfiable, otherwise [Unsat]. *)


val check_valid  : SolverOptions.t -> TSLExpression.formula -> Valid.t
(** [check_valid opt phi] checks the validity of formula [phi],
    assuming the options described in [opt]. It returns [Valid] if the
    formula is valid, otherwise [Invalid]. *)

  
val check_sat_plus_info : SolverOptions.t ->
                          TSLExpression.formula -> (Sat.t * int * DP.call_tbl_t)
(** [check_sat_plus_info opt phi] checks the satisfiability of
    formula [phi], assuming the options described in [opt]. It returns
    three values. The first value indicates whether the formula is
    satisfiable. The second value is the number of calls made to the TSL
    decision procedure (generally 1) and the third argument is the number
    of calls made to a TSLK decision procedure, which aids the TSL
    decision procedure. *)


val check_valid_plus_info : SolverOptions.t ->
                            TSLExpression.formula -> (Valid.t * int * DP.call_tbl_t)
(** [check_valid opt phi] checks the validity of formula [phi], assuming
    the options described in [opt]. It returns three values. The first value
    indicates whether the formula is satisfiable. The second value is the
    number of calls made to the TSL decision procedure (generally 1) and
    the third argument is the number of calls made to a TSLK decision
    procedure, which aids the TSL decision procedure. *)


val compute_model: bool -> unit
(** [compute_model b] enables or disables the computation of a model in
    case a counter example is found. *)


val model_to_str : unit -> string
(** [model_to_str ()] returns a string representing the model of the
    counter example found in the last call to the decision procedure. *)


val print_model  : unit -> unit
(** [print_model ()] prints in the standard output the result of
    [model_to_str ()]. *)


val get_sort_map : unit -> GenericModel.sort_map_t
(** [get_sort_map ()] returns the map from identifiers to sorts computed
    in the last call of the decision procedure. *)


val get_model  : unit -> GenericModel.t
(** [get_model ()] returns the model computed at the last call to the
   decision procedure. *)


val set_forget_primed_mem : bool -> unit
(** [set_forget_primed_mem b] indicates whether primed memory variables
    should be taken or not in consideration when computing the SMP. *)


val set_group_vars : bool -> unit
(** [set_group_vars b] indicates whether variables should be group in
    equivalence classes according to the information retrieved from the
    formula, in order to reduce the domain space when computing the SMP. *)
