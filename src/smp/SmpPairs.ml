
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


module PE = PairsExpression
module ASet = PE.AtomSet
module V = PE.V
module VarSet = V.VarSet
module F = Formula
module MS = ModelSize



(* Normal cutoff strategy *)

(* calculates the cut_off *)
let cut_off_normalized (expr:PE.conjunctive_formula) : MS.t =
  let vars = PE.get_varset_from_conj expr in
  let vars_tid = VarSet.cardinal (V.varset_of_sort vars PE.Tid) in
  let vars_int = VarSet.cardinal (V.varset_of_sort vars PE.Int) in
  let numint = ref (vars_int) in
  let numtid = ref (vars_tid) in

  let process_ineq (x,_) =
    match x with
    | PE.IntV _     -> ()                         (* nothing, y must be a VarT as well *)
    | PE.PairV _    -> (numint := !numint + 2; numtid := !numtid + 2) (* witness of pair inequality *) 
    | PE.SetV _     -> (incr numint)              (* the witness of s1 != s2 *)
    | PE.SetPairV _ -> (incr numint; incr numtid) (* the witness of s1 != s2 *)
  in
  let process (lit:PE.literal) =
    match lit with
    | F.Atom(PE.InEq(x,y)) -> process_ineq(x,y)
    | F.Atom a ->
        begin
          match a with
          | PE.InTidPair _ -> (incr numint)
          | PE.InIntPair _ -> (incr numtid)
          | _           -> ()
        end
    | F.NegAtom a ->
        begin
          match a with
          | PE.Less _         -> ()
          | PE.LessEq _       -> ()
          | PE.Greater _      -> ()
          | PE.GreaterEq _    -> ()
          | PE.LessTid _      -> ()
          | PE.In _           -> ()
          | PE.Subset _       -> (incr numint) (* witness of s1 \not\sub s2 *)
          | PE.InIntPair _    -> ()
          | PE.InTidPair _    -> ()
          | PE.InPair _       -> ()
          | PE.SubsetEqPair _ -> (incr numint; incr numtid) (* witness pair of s1 \not\sub s2 *)
          | PE.Eq(x,y)        -> process_ineq (x,y)
          | PE.InEq _         -> ()
          | PE.TidEq _        -> ()
          | PE.TidInEq _      -> ()
          | PE.FunEq _        -> ()
          | PE.FunInEq _      -> ()
          | PE.UniqueInt _    -> (incr numtid; numint := !numint + 2) (* witness of non uniqueness of integers in a pair *)
          | PE.UniqueTid _    -> (incr numint; numtid := !numtid + 2) (* witness of non uniqueness of tids in a pair *)
          | PE.PC _           -> ()
          | PE.PCUpdate _     -> ()
          | PE.PCRange _      -> ()
        end
  in
    match expr with
    | F.TrueConj  -> MS.create_with [(MS.Int, 1); (MS.Tid, 1)]
    | F.FalseConj -> MS.create_with [(MS.Int, 1); (MS.Tid, 1)]
    | F.Conj l    -> (List.iter process l;
                      MS.create_with [(MS.Int, !numint); (MS.Tid, !numtid)])


let compute_max_cut_off (conj_list:PE.conjunctive_formula list) : MS.t =
  let ms = MS.create () in
  List.iter (fun e ->
    let e_cut_off = cut_off_normalized e in
    MS.max_of ms e_cut_off
  ) conj_list;
  ms




(* Pruning SMP *)

let prune_atom (a:PE.atom) : PE.atom option =
  match a with
  | PE.Less _         -> None
  | PE.Greater _      -> None
  | PE.LessEq _       -> None
  | PE.GreaterEq _    -> None
  | PE.LessTid _      -> None 
  | PE.In _           -> None
  | PE.Subset _       -> Some a
  | PE.InTidPair _    -> Some a
  | PE.InIntPair _    -> Some a
  | PE.InPair _       -> Some a
  | PE.SubsetEqPair _ -> Some a
  | PE.Eq _           -> Some a
  | PE.InEq _         -> Some a
  | PE.TidEq _        -> Some a
  | PE.TidInEq _      -> Some a
  | PE.FunEq _        -> Some a
  | PE.FunInEq _      -> Some a
  | PE.UniqueInt _    -> Some a
  | PE.UniqueTid _    -> Some a
  | PE.PC _           -> None
  | PE.PCUpdate _     -> None
  | PE.PCRange _      -> None


let compute_max_cut_off_with_pruning (phi:PE.formula) : MS.t =
  let pruned_phi = LeapLib.Option.default F.True (F.prune_formula prune_atom (F.nnf phi)) in
  let new_dnf = List.map F.cleanup_conj (F.dnf pruned_phi) in
  let ms = if !LeapDebug._testing_ then
             LeapDebug._testing_smp_()
           else
             compute_max_cut_off (new_dnf) in
  LeapVerbose.verbstr (MS.to_str ms);
  ms

    
let cut_off (phi:PE.formula) : MS.t =
  (* LOG "Strategy: %s\n" (Smp.strategy_to_str strat) LEVEL DEBUG; *)
  compute_max_cut_off_with_pruning phi
