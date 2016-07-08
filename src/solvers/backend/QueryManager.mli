
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



open NumQuery
open PairsQuery
open TllQuery

(** [set_smt_usage b] flags the usage of SMT-LIB translation if available
    to [b] *)
val set_smt_usage : bool -> unit


(** [get_num_query id] returns an appropriate numeric query module for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
val get_num_query : string -> (module NUM_QUERY)


(** [get_pairs_query id] returns an appropriate query module over pairs for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
val get_pairs_query : string -> (module PAIRS_QUERY)


(** [get_tll_query id] returns an appropriate TLL query module for the
    backend solver identified by [id] depending on the status previously set
    through a call to [set_smt_usage] *)
val get_tll_query : string -> (module TLL_QUERY)

