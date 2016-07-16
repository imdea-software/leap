
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
open YicesNumQuery
open Z3NumQuery
open YicesPairsQuery
open Z3PairsQuery
open YicesTllQuery
open Z3TllQuery
open SMTTllQuery

let use_smtlib = ref false


let set_smt_usage (b:bool) : unit =
  use_smtlib := b


let get_num_query (id:string) : (module NUM_QUERY) =
  match (id,!use_smtlib) with
  | ("Yices", _) -> (module YicesNumQuery)
  | ("Z3",    _) -> (module Z3NumQuery)
  | _            -> (module YicesNumQuery)


let get_pairs_query (id:string) : (module PAIRS_QUERY) =
  match (id,!use_smtlib) with
  | ("Yices", _) -> (module YicesPairsQuery)
  | ("Z3",    _) -> (module Z3PairsQuery)
  | _            -> (module YicesPairsQuery)


let get_tll_query (id:string) : (module TLL_QUERY) =
  match (id,!use_smtlib) with
  | (_,       true ) -> (module SMTTllQuery)
  | ("Z3",    false) -> (module Z3TllQuery)
  | ("Yices", false) -> (module YicesTllQuery)
  | _                -> (module Z3TllQuery)

