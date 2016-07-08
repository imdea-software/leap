
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


module F = Formula
module NE = NumExpression
module Arr = Arrangements
module GM = GenericModel
module GenSet = LeapGenericSet

let numSolver : (module NumSolver.S) =
  NumSolver.choose BackendSolvers.Yices.identifier

module NumSolver = (val numSolver)

type t =
  {
    domain : NE.integer GenSet.t;
    original_constraint : NE.formula;
    mutable learnt_constraints : NE.formula list;
  }


module IntSet = Set.Make(
  struct
    let compare = fun a b -> Pervasives.compare b a
    type t = int
  end )


let gen_orig_constraints (arr:NE.integer Arr.t) : NE.formula =
  let eqs_xs = GenSet.fold (fun (a,b) xs ->
                 F.Atom (NE.Eq (NE.IntV a, NE.IntV b)) :: xs
               ) (Arr.get_eqs arr) [] in
  let ineqs_xs = GenSet.fold (fun (a,b) xs ->
                   F.Atom (NE.InEq (NE.IntV a, NE.IntV b)) :: xs
                 ) (Arr.get_ineqs arr) eqs_xs in
  let order_xs = Hashtbl.fold (fun a b xs ->
                   F.Atom (NE.Less (a,b)) :: xs
                 ) (Arr.get_order arr) ineqs_xs in
  let succ_xs = Hashtbl.fold (fun a b xs ->
                  F.Atom (NE.Eq (NE.IntV (NE.Add(a,NE.Val 1)), NE.IntV b)) :: xs
                ) (Arr.get_succ arr) order_xs in
  let leq_xs = List.fold_left (fun xs (a,b) ->
                 F.Atom (NE.LessEq (a,b)) :: xs
               ) succ_xs (Arr.get_leq arr) in
  let min_xs = match Arr.get_minimum arr with
               | None -> leq_xs
               | Some m -> GenSet.fold (fun a xs ->
                             F.Atom (NE.LessEq (m,a)) :: xs
                           ) (Arr.get_domain arr) leq_xs in
  F.conj_literals min_xs


let new_arr_gen (arr:NE.integer Arr.t) : t =
  let orig_const = gen_orig_constraints arr in
  NumSolver.compute_model true;
  (*
  print_endline "NEW ARRANGEMENT";
  print_endline "==============================================";
  GenSet.iter (fun i -> print_endline (match i with NE.Var v -> (NE.V.to_full_str (fun _ -> "") (fun _ -> "") v) | _ -> "")) (Arr.get_domain arr);
  print_endline "==============================================";
  *)
  {
    domain = Arr.get_domain arr;
    original_constraint = orig_const;
    learnt_constraints = [];
  }


let find_arrg (ag:t) : NE.integer list list =

  (*
  print_endline "FIND_ARRG";
  print_endline "==============================================";
  GenSet.iter (fun i -> print_endline (match i with NE.Var v -> (NE.V.to_full_str (fun _ -> "") (fun _ -> "") v) | _ -> "")) (ag.domain);
  print_endline "==============================================";
  *)


  (*
   print_endline ("Calling find_arrg");
   print_endline (GenSet.to_str NE.integer_to_str ag.domain);
  *)
  
  (* Auxiliary function for creating order inequalities *)
  let rec ineq_f (is:NE.integer list list) : NE.literal list =
    match is with
    | xs::ys::zs -> F.Atom (NE.Less (List.hd xs, List.hd ys))::(ineq_f (List.tl is))
    | _ -> [] in
  (* 1. Create the formula for the query *)
  let phi = F.conj_list (ag.original_constraint :: ag.learnt_constraints) in
  (*
  print_endline ("Going to check formula: " ^ (NE.formula_to_str phi));
  *)
  (* 2. Check whether there exists a model of such formula *)
  if Sat.is_sat (NumSolver.check_sat phi) then begin
    (* 3. There exists a model that satisfies the arrangement conditions *)
    let model = NumSolver.get_model () in
    let map = NumSolver.get_sort_map () in
    let elems = GM.sm_dom_of_type map (GM.Const GM.int_s) in
    let intMap = Hashtbl.create 16 in
    let set = List.fold_left (fun s e ->
                let len = (String.length e) - 1 in
                let v = if e.[len] == '\'' then
                          NE.Var (NE.build_var (String.sub e 0 len) NE.Int true
                                  NE.V.Shared NE.V.GlobalScope)
                        else
                          NE.Var (NE.build_var e NE.Int false
                                  NE.V.Shared NE.V.GlobalScope) in
                let value = try
                              match GM.get_const model e with
                              | GM.Single x -> int_of_string x
                              | _ -> max_int
                            with _ -> max_int in
                Hashtbl.add intMap value v;
                IntSet.add value s
              ) IntSet.empty elems in
    let (eqs,res) = IntSet.fold (fun i (cs,xs) ->
                      let eqset = Hashtbl.find_all intMap i in
                      let cs' =
                        match eqset with
                        | [] -> cs
                        | _ -> begin
                                 let h = List.hd eqset in
                                 List.fold_left (fun ys x ->
                                   F.Atom (NE.Eq (NE.IntV h, NE.IntV x)) :: ys
                                 ) cs (List.tl eqset)
                               end in
                      (cs', eqset::xs)
                    ) set ([],[]) in

    let conjs = eqs @ (ineq_f res) in
    ag.learnt_constraints <- F.Not (F.conj_literals conjs) :: ag.learnt_constraints;

    (* DEBUG *)

    (*
    print_endline "RES";
    print_endline "==============================================";
    let str = "[" ^ String.concat ";"
                (List.map (fun xs ->
                  "[" ^ (String.concat "," (List.map (fun i -> (match i with NE.Var v -> (NE.V.to_full_str (fun _ -> "") (fun _ -> "") v) | _ -> "")) xs)) ^ "]"
                 ) res) ^ "]" in
    print_endline str;


    print_endline "==============================================";
    *)


  (*
    let str = "[" ^ String.concat ";"
                (List.map (fun xs ->
                  "[" ^ (String.concat "," (List.map NE.integer_to_str xs)) ^ "]"
                 ) res) ^ "]" in
    print_endline str;
    *)
    (* DEBUG *)
    res
  end else
    (* No model of the restrictions, then nothing to be done. *)
    []


let next_arr (ag:t) : NE.integer list list =
  List.rev (find_arrg ag)
