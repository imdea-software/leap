
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



type inv_t = System.var_table_t * Tag.f_tag option * Expression.formula
type results_t =int * int * int * int * int * int * int * int *
                int * int * int * int * string

type vc_status = NotVerified | NotValid | IsValid | Unneeded

type status_t = Unverified | Invalid | Valid of DP.t

val report_generated_vcs : Tactics.vc_info list -> int -> unit
val report_inv_cand : Expression.formula -> unit
val report_system : System.t -> unit
val report_sup_inv : inv_t list -> unit
val report_gen_sup_inv : Expression.formula -> unit
val report_results : results_t -> unit

val report_vc_run_header : unit -> unit
val report_vc_run : int -> vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float ->
                           vc_status -> float -> string -> unit
val report_analysis_time : float -> unit
val report_labels : System.label_table_t -> unit

(* ALE: TODO: I may need to extend this function in order to get values
        from TSLK and TSL. *)
val report_details_to_file : string -> string -> string ->
                             (int * Expression.pc_t * int) -> Tag.f_tag list ->
                             bool -> (string * float) list -> unit


val report_vc_header : int -> Tactics.vc_info -> int -> unit
val report_vc_tail : int -> Result.info_t list -> DP.call_tbl_t -> unit
val report_obligation_header : int -> Expression.formula -> unit
val report_obligation_tail : Result.status_t -> float -> unit
val report_summary : int -> Result.info_t list -> DP.call_tbl_t -> unit
