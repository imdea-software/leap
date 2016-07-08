
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


module type S =
  sig

    module V : Variable.S
    type t
    type term
    type formula

    val new_norm : formula -> t

    val add_term_map : t -> term -> V.t -> unit
    val remove_term_map : t -> term -> unit
    val is_mapped : t -> term -> bool
    val find_term_map : t -> term -> V.t
    val gen_if_not_var : t -> (term -> bool) -> (term -> V.t) -> term -> V.sort -> V.t
    val term_map_size : t -> int
    val iter_term_map : (term -> V.t -> unit) -> t -> unit

    val add_proc_term_map : t -> term -> V.t -> unit
    val find_proc_term : t -> term -> V.t

    val gen_fresh_var : t -> V.sort -> V.t
    val to_str : t -> (term -> string) -> (V.t -> string) -> string

  end

module Make (Opt:NormSpec.S) : S
  with type term = Opt.norm_term
  with type formula = Opt.norm_formula
  with type V.t = Opt.VS.t
  with type V.sort = Opt.VS.sort
