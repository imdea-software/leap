
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


module type CUSTOM_TSLKSOLVER = sig
  module TslkExp : ExpressionTypes.TSLKEXP
 
  
  val check_sat_conj  : SolverOptions.t -> TslkExp.conjunctive_formula -> Sat.t
  val check_sat_dnf   : SolverOptions.t -> TslkExp.formula -> Sat.t
  
  val check_valid_dnf : SolverOptions.t -> TslkExp.formula -> Valid.t
  val check_valid_dnf_pus_info : SolverOptions.t -> TslkExp.formula -> (Valid.t * int)
    
  val check_sat : SolverOptions.t -> TslkExp.formula -> Sat.t
  val check_valid : SolverOptions.t -> TslkExp.formula -> Valid.t
  
  val check_valid_plus_info : SolverOptions.t -> TslkExp.formula -> (Valid.t * int)

  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model : unit -> GenericModel.t

  val set_forget_primed_mem : bool -> unit
  val set_group_vars : bool -> unit
end

module type S = CUSTOM_TSLKSOLVER


module Make (K : Level.S)
            (Solver : BackendSolverIntf.BACKEND_TSLK) : S

val choose : string -> int -> (module S)
