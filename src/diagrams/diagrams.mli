
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


type pvd_vc_t

type gen_t

val new_options : Expression.PosSet.t ->
                  PVD.conditions_t list ->
                  PVD.node_id_t list ->
                  gen_t

module type S =
  sig
    val gen_vcs : ?opt:gen_t option ->
                  PVD.t ->
                  pvd_vc_t
    val gen_from_pvd : ?opt:gen_t option ->
                       PVD.t ->
                       PVD.support_t option ->
                       Core.proof_obligation_t list
    val solve_from_pvd : ?opt:gen_t option ->
                         PVD.t ->
                         PVD.support_t option ->
                         Core.solved_proof_obligation_t list
  end

module Make (C:Core.S) : S
