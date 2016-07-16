
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

    type term
    type formula
    module V : Variable.S
    type t

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


module Make (Opt:NormSpec.S) =
  struct

    type atom = Opt.norm_atom
    type term = Opt.norm_term
    type formula = Opt.norm_formula
    module V = Opt.VS

    type t =
      {
        term_map : (term, V.t) Hashtbl.t ;
        processed_term_map : (term, V.t) Hashtbl.t ;
        fresh_gen_info : V.fresh_var_gen_t ;
      }


    let new_fresh_gen_from_formula (phi:formula) : V.fresh_var_gen_t =
      let vars = V.VarSet.fold (fun v s ->
                   V.VarIdSet.add (V.id v) s
                 ) (Opt.norm_varset phi) V.VarIdSet.empty in
      V.new_fresh_gen vars



    let new_norm (phi:formula) : t =
      {
        term_map = Hashtbl.create 10 ;
        processed_term_map = Hashtbl.create 10 ;
        fresh_gen_info = new_fresh_gen_from_formula phi ;
      }



    let add_term_map (info:t) (t:term) (v:V.t) : unit =
      Hashtbl.add info.term_map t v


    let remove_term_map (info:t) (t:term) : unit =
      Hashtbl.remove info.term_map t


    let is_mapped (info:t) (t:term) : bool =
      Hashtbl.mem info.term_map t


    let find_term_map (info:t) (t:term) : V.t =
      Hashtbl.find info.term_map t


    let term_map_size (info:t) : int =
      Hashtbl.length info.term_map


    let iter_term_map (f:term -> V.t -> unit) (info:t) : unit =
      Hashtbl.iter f info.term_map


    let add_proc_term_map (info:t) (t:term) (v:V.t) : unit =
      Hashtbl.add info.processed_term_map t v


    let find_proc_term (info:t) (t:term) : V.t =
      Hashtbl.find info.processed_term_map t


    let gen_fresh_var (info:t) (s:V.sort) : V.t =
      V.gen_fresh_var Opt.norm_fresh_vname (Opt.norm_fresh_vinfo()) info.fresh_gen_info s


    let gen_if_not_var (info:t)
                       (is_var : term -> bool)
                       (term_to_var : term -> V.t)
                       (t:term)
                       (s:V.sort) : V.t =
      let append_if_diff (t:term) (v:V.t) : unit =
        if is_var t then
          (if (term_to_var t) <> v then add_term_map info t v)
        else
          add_term_map info t v in
      if is_var t then
        term_to_var t
      else try
             try
               find_proc_term info t
             with _ -> find_term_map info t
           with _ -> begin
                       let v = gen_fresh_var info s in
                       append_if_diff t v;
                       v
                     end


    let to_str (info:t) (term_to_str:term -> string) (var_to_str:V.t -> string) : string =
      let map_str (map:(term,V.t) Hashtbl.t) =
        Hashtbl.fold (fun t v str ->
          str ^ (term_to_str t) ^ "  -->  " ^ (var_to_str v) ^ "\n"
        ) map "" in
      let term_map_str = map_str info.term_map in
      let processed_terms_str = map_str info.processed_term_map in
      ("=================================\n" ^
       "TERM MAP:\n" ^
       term_map_str ^
       "PROCESSED TERMS:\n" ^
       processed_terms_str ^ "\n" ^
       "=================================\n")

  end

