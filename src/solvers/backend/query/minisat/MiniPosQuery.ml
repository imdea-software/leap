
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


open LeapLib
open Printf

module PE = PosExpression

let prog_lines : int ref = ref 0
(** The number of lines in the program *)

let set_prog_lines (n:int) : unit =
  prog_lines := n

let pos_expression_to_str (expr:PE.expression) : string =
  let id_count = ref 1 in
  let expr_map : (PE.expression, int) Hashtbl.t = Hashtbl.create 10 in
  let lookup (expr:PE.expression) : int =
    let (neg, e) = match expr with
                     PE.Not t -> (true , t   )
                   | _           -> (false, expr) in
    let es = match e with
               PE.Eq (e1,e2)    -> [PE.Eq(e1,e2); PE.Eq (e2,e1)]
             | PE.InEq (e1, e2) -> [PE.InEq(e1,e2); PE.InEq(e2, e1)]
             | _                   -> [e] in
    let id = if List.exists (Hashtbl.mem expr_map) es then
               (List.fold_left (fun id x ->
                 try
                   Hashtbl.find expr_map x
                 with
                   Not_found -> id
               ) (-1) es)
             else
               let i = !id_count in
               let _ = incr id_count in
               let _ = Hashtbl.add expr_map e i in i in
    let _ = assert (id >=0)
    in
      if neg then -id else id in
  let expand_form = PE.expand_pc_range expr in
  let expr_voc = PE.voc expr in
  (* All threads are at some location *)
  let some_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              some_pos_list := PE.PC (i,PE.V.Local (PE.voc_to_var t),false) :: !some_pos_list
            ) expr_voc
          done in
  let some_pos = match !some_pos_list with
                 | [] -> PE.True
                 | _  -> PE.disj_list !some_pos_list in
  (* All threads are at an unique location *)
  let unique_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              let not_pos = ref [] in
              let not_pos' = ref [] in
              let t_as_var = PE.voc_to_var t in
              let _ = for j=1 to !prog_lines do
                        if i!=j then
                          begin
                            not_pos := PE.Not(PE.PC(j,PE.V.Local t_as_var,false))
                                          :: !not_pos;
                            not_pos':= PE.Not(PE.PC(j,PE.V.Local t_as_var,true))
                                          :: !not_pos'
                          end
                      done in
              let no_other_pos = PE.conj_list !not_pos in
              let no_other_pos' = PE.conj_list !not_pos' in
              let impl = PE.Implies (PE.PC (i,PE.V.Local t_as_var,false),
                                        no_other_pos) in
              let impl' = PE.Implies (PE.PC (i,PE.V.Local t_as_var,true),
                                         no_other_pos')
              in
                unique_pos_list := impl :: impl' :: !unique_pos_list
            ) expr_voc
          done in
  let unique_pos = PE.conj_list !unique_pos_list in
  (* Compute CNF and translate to SAT *)
  let full_formula = PE.And (some_pos, PE.And(unique_pos, expand_form)) in
  let cnf_form = PE.cnf full_formula in
  let desc_str = sprintf "c SAT description for location reasoning \
                          on formula:\nc %s\n" (PE.expr_to_str full_formula) in
  let expr_str = List.fold_left (fun str xs ->
                   str ^ (String.concat " " $
                            List.map (fun t ->
                              string_of_int (lookup t)
                            ) xs)
                       ^ " 0\n"
                 ) "" cnf_form in
  let header_str = sprintf "p cnf %i %i\n" (Hashtbl.length expr_map)
                                           (List.length cnf_form)

  in
    desc_str ^ header_str ^ expr_str
