(*

module PE = PairsExpression

module Varset = PE.V.VarSet



let cut_off_normalized (expr:PE.conjunctive_formula) : MS.t =
  let vars = PE.get_varset_from_conj expr in
  let vars_tid_set = VarSet.varset_of_sort vars PE.Tid in
  let vars_tid = VarSet.cardinal vars_tid_set in
  let vars_int_set = V.varset_of_sort vars PE.Int in
  let vars_int = VarSet.cardinal vars_addr_set in
  {
    num_tids = vars_tid;
    num_ints = vars_int;
  }


let int_counter = ref 1
let tid_counter = ref 1

let cut_off (f:PE.formula) : (int * int) =
  let rec cut_off_integer (i:PE.integer) =
    match i with
    | PE.Var _       -> incr int_counter
    | PE.Val _       -> ()
    | PE.Neg j       -> cut_off_integer j
    | PE.Add (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Sub (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Mul (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.Div (j1,j2) -> (cut_off_integer j1; cut_off_integer j2)
    | PE.SetMin _    -> incr int_counter
    | PE.SetMax _    -> incr int_counter
    | PE.PairInt p   -> cut_off_pair p
    | _                   -> ()
  and cut_off_tid (t:PE.tid) =
    match t with
    | PE.VarTh _     -> incr tid_counter
    | PE.NoTid       -> ()
    | PE.PairTid p   -> cut_off_pair p
  and cut_off_pair (p:PE.pair) =
    match p with
    | PE.VarPair _   -> ()
    | PE.IntTidPair (i,t) -> (cut_off_integer i; cut_off_tid t)
    | PE.SetPairMin (sp) -> ()
    | PE.SetPairMax (sp) -> () in
  let cut_off_atom (a:PE.atom) =
    match a with
    | PE.Less(i1,i2)      -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.Greater(i1,i2)   -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.LessEq(i1,i2)    -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.GreaterEq(i1,i2) -> (cut_off_integer i1);(cut_off_integer i2)
    | PE.LessTid (t1,t2)  -> (cut_off_tid t1);(cut_off_tid t2)
    | PE.In(i,s)          -> (cut_off_integer i)
    | PE.Subset _         -> incr int_counter
    | PE.InTidPair (t,sp) -> (incr int_counter; cut_off_tid t)
    | PE.InIntPair (i,sp) -> (incr tid_counter; cut_off_integer i)
    | PE.UniqueTid sp     -> (incr tid_counter)
    | PE.UniqueInt sp     -> (incr int_counter)
    | PE.InEq (PE.SetV _, PE.SetV _) -> incr int_counter
    | PE.FunInEq (PE.FunVar v, _)     ->
          if (PE.V.sort v) = PE.Set then incr int_counter
    | PE.FunInEq (PE.FunUpd (_,_,t),_)    ->
          begin
            match t with
              PE.SetV _ -> incr int_counter
            | _              -> ()
          end


    | _                                             -> () in

  let cutoff_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun info a -> cut_off_atom a)
                    (fun info -> ())
                    (fun a b -> a;b) in

  let cut_off_formula (phi:PE.formula) : unit =
    let m = cut_off_normalized (Formula.Conj (Formula.to_conj_literals phi)) in
    (m.num_tids, m.num_ints)
    (*
    Formula.formula_fold cutoff_fs () phi in

  let _ = cut_off_formula f
  in
    (!tid_counter, !int_counter)
*)









let union_eq_cutoff (info:union_info) ((x,y):(Expr.term * Expr.term)) : union_info =
  match x with
    VarT _      -> info (* nothing, y must be a VarT as well *)
  | SetT _      -> union_count_addr info (Expr.Eq(x,y)) (* the witness of s1 != s2 *)
  | ElemT _     -> info
  | TidT _     -> info
  | AddrT _     -> info (* no need to look for firstlock, every firstlock has a var *)
  | CellT _     -> info
  | SetThT _    -> union_count_tid info (Expr.Eq(x,y)) (* the witness of st1 != st2 *)
  | SetElemT _  -> union_count_elem info (Expr.Eq(x,y)) (* the witness of se1 != se2 *)
  | PathT _     -> union_count_addr info (Expr.Eq(x,y)) (* the witnesses of p1 != p2 *)
  | MemT _      -> info
  | IntT _      -> info
  | VarUpdate _ -> info (* ALE: Not sure if OK *)


let union_ineq_cutoff (info:union_info) ((x,y):(Expr.term * Expr.term)) : union_info =
  match x with
    VarT _      -> info (* nothing, y must be a VarT as well *)
  | SetT _      -> union_count_addr info (Expr.InEq(x,y)) (* the witness of s1 != s2 *)
  | ElemT _     -> info
  | TidT _     -> info
  | AddrT _     -> info (* no need to look for firstlock, every firstlock has a var *)
  | CellT _     -> info
  | SetThT _    -> union_count_tid info (Expr.InEq(x,y)) (* the witness of st1 != st2 *)
  | SetElemT _  -> union_count_elem info (Expr.InEq(x,y)) (* the witness of se1 != se2 *)
  | PathT _     -> union_count_addr info (Expr.InEq(x,y)) (* the witnesses of p1 != p2 *)
  | MemT _      -> info
  | IntT _      -> info
  | VarUpdate _ -> info (* ALE: Not sure if OK *)


let union_atom_cutoff_pol (pol:Polarity.t) (info:union_info) (a:Expr.atom) : union_info =
  match a with
    Append _       -> if Polarity.is_pos pol then info else union_count_addr info a
  | Reach _        -> union_count_addr info a
  | OrderList _    -> if Polarity.is_pos pol then info else union_count_elem info a
  | In      _      -> info
  | SubsetEq _     -> if Polarity.is_pos pol then info else union_count_addr info a
  | InTh _         -> info
  | SubsetEqTh _   -> if Polarity.is_pos pol then info else union_count_tid info a
  | InElem _       -> info
  | SubsetEqElem _ -> if Polarity.is_pos pol then info else union_count_elem info a
  | Less _         -> info
  | LessEq _       -> info
  | Greater _      -> info
  | GreaterEq _    -> info
  | LessElem _     -> union_count_elem info a
  | GreaterElem _  -> union_count_elem info a
  | Eq e           -> if Polarity.is_pos pol then info else union_eq_cutoff info e
  | InEq e         -> if Polarity.is_neg pol then info else union_ineq_cutoff info e
  | BoolVar _      -> info
  | PC _           -> info
  | PCUpdate _     -> info
  | PCRange _      -> info



let union_literal_cutoff_pol (pol:Polarity.t) (info:union_info) (l:Expr.literal) : union_info =
  match l with
    F.Atom a    -> union_atom_cutoff_pol pol info a
  | F.NegAtom a -> union_atom_cutoff_pol (Polarity.invert pol) info a


let rec union_formula_cutoff_pol (pol:Polarity.t) (info:union_info) (phi:Expr.formula) : union_info =
  let apply_cut = union_formula_cutoff_pol in
  match phi with
  | F.Literal l       -> union_literal_cutoff_pol pol info l
  | F.True            -> info
  | F.False           -> info
  | F.And (f1,f2)     -> apply_cut pol (apply_cut pol info f1) f2
  | F.Or (f1,f2)      -> apply_cut pol (apply_cut pol info f1) f2
  | F.Not f           -> apply_cut (Polarity.invert pol) info f
  | F.Implies (f1,f2) -> apply_cut pol (apply_cut (Polarity.invert pol) info f1) f2
  | F.Iff (f1,f2)     -> apply_cut Polarity.Both (apply_cut Polarity.Both info f2) f2


let union_formula_cutoff (info:union_info) (phi:Expr.formula) : union_info =
  union_formula_cutoff_pol Polarity.Pos info phi
*)




module PE = PairsExpression
module ASet = PE.AtomSet
module V = PE.V
module VarSet = V.VarSet
module F = Formula
module MS = ModelSize



type union_info = (ASet.t * ASet.t)


let new_union_count = (ASet.empty, ASet.empty)


(* Normal cutoff strategy *)
let compute_max_cut_off (conj_list:PE.conjunctive_formula list) : MS.t =
  MS.create ()


(* Union SMP *)

let union_model_size (u:union_info) : MS.t =
  let ms = MS.create () in
  let (i_set, t_set) = u in
  MS.add ms MS.Int (ASet.cardinal i_set);
  MS.add ms MS.Tid (ASet.cardinal t_set);
  ms


let rec union_formula_cutoff_pol (pol:Polarity.t) (info:union_info) (phi:PE.formula) : union_info =
  (ASet.empty, ASet.empty)
  (*
  let apply_cut = union_formula_cutoff_pol in
  match phi with
  | F.Literal l       -> union_literal_cutoff_pol pol info l
  | F.True            -> info
  | F.False           -> info
  | F.And (f1,f2)     -> apply_cut pol (apply_cut pol info f1) f2
  | F.Or (f1,f2)      -> apply_cut pol (apply_cut pol info f1) f2
  | F.Not f           -> apply_cut (Polarity.invert pol) info f
  | F.Implies (f1,f2) -> apply_cut pol (apply_cut (Polarity.invert pol) info f1) f2
  | F.Iff (f1,f2)     -> apply_cut Polarity.Both (apply_cut Polarity.Both info f2) f2
  *)



let union_formula_cutoff (info:union_info) (phi:PE.formula) : union_info =
  union_formula_cutoff_pol Polarity.Pos info phi


let compute_max_cut_off_with_union (phi:PE.formula) : MS.t =
  let vars = PE.get_varset_from_formula phi in
  let vartid_num  = VarSet.cardinal (V.varset_of_sort vars PE.Tid) in
  let varint_num = VarSet.cardinal (V.varset_of_sort vars PE.Int) in
  let varsetpair_num = VarSet.cardinal (V.varset_of_sort vars PE.SetPair) in
  let info = union_model_size (union_formula_cutoff new_union_count phi) in
  let num_ints = varint_num +                   (* Address variables      *)
                 varsetpair_num * vartid_num +  (* Set of pairs variables *)
                 (MS.get info MS.Int)           (* Special literals       *) in
  let num_tids = 1 +                            (* No thread              *)
                 vartid_num +                   (* Tid variables          *)
                 varsetpair_num  * varint_num + (* Set of pairs variables *)
                 (MS.get info MS.Tid)           (* Cell locks             *)
  in
    MS.create_with [(MS.Int, num_ints); (MS.Tid, num_tids)]


    
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
    compute_max_cut_off (new_dnf)

    
let cut_off (phi:PE.formula) : MS.t =
(*  LOG "Strategy: %s\n" (Smp.strategy_to_str strat) LEVEL DEBUG; *)
  compute_max_cut_off_with_pruning phi
