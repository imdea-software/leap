
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


module type CUSTOM_PAIRSSOLVER = sig
  module PairsExp : ExpressionTypes.PAIRSEXP
    
  (* Basic invocations *)
  val check_sat              : PairsExp.formula -> Sat.t
  val check_valid            : PairsExp.formula -> Valid.t
  
  (* Invocations with extra information *)
  val check_valid_plus_info  : PairsExp.formula -> (Valid.t * int)
  
  val check_sat_with_lines   : int -> PairsExp.formula -> Sat.t
  val check_valid_with_lines : int -> PairsExp.formula -> Valid.t
  
  val check_valid_with_lines_plus_info 
                          : int -> PairsExp.formula -> (Valid.t * int)


  (* Counter models management *)
  val compute_model: bool -> unit
  val model_to_str : unit -> string
  val print_model  : unit -> unit
  val get_sort_map : unit -> GenericModel.sort_map_t
  val get_model    : unit -> GenericModel.t
end

module type S = CUSTOM_PAIRSSOLVER
  with module PairsExp = PairsExpression
  
module Make : functor (Solver : BackendSolverIntf.BACKEND_PAIRS) -> S

val choose : string -> (module S)
