
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



exception Unknown_strategy_str of string

type cutoff_strategy_t =
  | Dnf       (* Computes dnf over the formula and then counts literals *)
  | Union     (* Computes an upper bound using union over literals *)
  | Pruning   (* Computes a better bound, by pruning non interesting literals *)


type cutoff_options_t =
  {
    mutable forget_primed_mem : bool ;
    mutable group_vars : bool ;
  }


let def_strategy_list : cutoff_strategy_t list = [ Dnf; Union; Pruning]


let strategy_to_str (s:cutoff_strategy_t) : string =
  match s with
  | Dnf     -> "dnf"
  | Union   -> "union"
  | Pruning -> "pruning"


let str_to_strategy (str:string) : cutoff_strategy_t =
  match str with
  | "dnf"     -> Dnf
  | "union"   -> Union
  | "pruning" -> Pruning
  | s         -> raise(Unknown_strategy_str s)



(* Cutoff options functions *)

let opt_empty () =
  {
    forget_primed_mem = true ;
    group_vars = false ;
  }


let set_forget_primed_mem (opt:cutoff_options_t) (b:bool) : unit =
  opt.forget_primed_mem <- b


let set_group_vars (opt:cutoff_options_t) (b:bool) : unit =
  opt.group_vars <- b


let forget_primed_mem (opt:cutoff_options_t) : bool =
  opt.forget_primed_mem


let group_vars (opt:cutoff_options_t) : bool =
  opt.group_vars
