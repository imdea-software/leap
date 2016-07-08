
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


(*
open BackendSolverIntf

module type CUSTOM_BACKEND_POS_TLL_TSLK =
  sig
  include BackendCommon
  module Translate : sig
    include PosBackend  with type t := t
    include TllBackend  with type t := t
    include TslkBackend with type t := t
  end
end

module type BACKEND_POS_TLL_TSLK = CUSTOM_BACKEND_POS_TLL_TSLK
  with module Translate.Pos.Exp  = PosExpression
  and  module Translate.Tll.Exp  = TllExpression
  *)
