open LeapLib
open LeapVerbose


module Make (TSLK : TSLKExpression.S) =
  struct

    module Expr     = TSLK
    module V        = TSLK.V
    module VarSet   = V.VarSet
    module ASet     = TSLK.AtomSet
    module F        = Formula
    module MS       = ModelSize


    type union_info = (ASet.t * ASet.t * ASet.t * ASet.t)

    let options : Smp.cutoff_options_t ref = ref (Smp.opt_empty())

    (* union_info functions *)

    let new_union_count = (ASet.empty, ASet.empty, ASet.empty, ASet.empty)


    let union_count_elem (u:union_info) (a:Expr.atom) : union_info =
      let (e_set, t_set, a_set, l_set) = u
      in
        (ASet.add a e_set, t_set, a_set, l_set)


    let union_count_tid (u:union_info) (a:Expr.atom) : union_info =
      let (e_set, t_set, a_set, l_set) = u
      in
        (e_set, ASet.add a t_set, a_set, l_set)


    let union_count_addr (u:union_info) (a:Expr.atom) : union_info =
      let (e_set, t_set, a_set, l_set) = u
      in
        (e_set, t_set, ASet.add a a_set, l_set)


    let union_count_level (u:union_info) (a:Expr.atom) : union_info =
      let (e_set, t_set, a_set, l_set) = u
      in
        (e_set, t_set, a_set, ASet.add a l_set)


    let union_model_size (u:union_info) : MS.t =
      let (e_set, t_set, a_set, l_set) = u in
      let ms = MS.create() in
      MS.add ms MS.Elem (ASet.cardinal e_set);
      MS.add ms MS.Tid (ASet.cardinal t_set);
      MS.add ms MS.Addr
        (ASet.cardinal a_set +
          (ASet.cardinal (ASet.filter (fun a ->
                          match a with
                          | Expr.OrderList _ -> true
                          | _ -> false
                         ) a_set)));
     MS.add ms MS.Level (ASet.cardinal l_set);
     ms


    let rec redundant_cell_vars (phi:Expr.formula) (aset:VarSet.t) : VarSet.t =
      match phi with
      | F.And (phi1,phi2) -> VarSet.union (redundant_cell_vars phi1 aset)
                                             (redundant_cell_vars phi2 aset)
      | F.Literal(F.Atom(Expr.Eq(Expr.CellT(Expr.VarCell c),
                                 Expr.CellT(Expr.MkCell(_,addrs,_)))))
      | F.Literal(F.NegAtom(Expr.InEq(Expr.CellT(Expr.VarCell c),
                                      Expr.CellT(Expr.MkCell(_,addrs,_))))) ->
        let addrsset = List.fold_left (fun s a -> match a with
                                                  | Expr.VarAddr v -> VarSet.add v s
                                                  | _              -> s
                                      ) (VarSet.empty) addrs in
        if VarSet.subset addrsset aset then VarSet.singleton c else VarSet.empty
      | _ -> VarSet.empty


    (* calculates the cut_off *)
    let cut_off_normalized (expr:Expr.conjunctive_formula) : MS.t =
      let vars = Expr.get_varset_from_conj expr in
      let vars_tid_set = V.varset_of_sort vars Expr.Tid in
      let vars_tid = VarSet.cardinal vars_tid_set in
      let vars_addr_set = V.varset_of_sort vars Expr.Addr in
      let vars_addr = VarSet.cardinal vars_addr_set in
      let vars_cell_set = V.varset_of_sort vars Expr.Cell in
      let vars_cell = VarSet.cardinal vars_cell_set in

      let vars_mem_set = if (Smp.forget_primed_mem !options &&
                             not (Smp.group_vars !options)) then
                           VarSet.filter (fun v -> not (V.is_primed v))
                             (V.varset_of_sort vars Expr.Mem)
                         else
                           V.varset_of_sort vars Expr.Mem in

      let vars_mem = VarSet.cardinal vars_mem_set in
      (* ALE: No need to add null and NoThread in the counter,
              as they are added separately as an special address
              and tid respectively when creating the query to SMT *)

      let numlevel = ref (Expr.k) in
      (* TOFIX: Not sure if I should consider all next pointers, or if they
                are already expressed through a variable *)
      let numtid = ref (vars_tid + vars_mem * vars_addr * !numlevel) in
(*      let numaddr = ref (vars_addr + vars_mem * vars_addr * !numlevel) in *)
(*
      Printf.printf "VARS ARRDS: %i\n" vars_addr;
      Printf.printf "VARS CELLS: %i\n" vars_cell;
      Printf.printf "NUMLEVEL: %i\n" !numlevel;
*)
      let numaddr = ref (vars_addr + vars_cell * !numlevel) in
      let vars_elem = VarSet.cardinal (V.varset_of_sort vars Expr.Elem) in
      let numelem = ref (vars_elem + vars_mem * vars_addr) in

      let process_ineq (x,_) =
        match x with
        | Expr.VarT _      -> ()        (* nothing, y must be a VarT as well *)
        | Expr.SetT _      -> numaddr := !numaddr + 1 (* the witness of s1 != s2 *)
        | Expr.ElemT _     -> ()
        | Expr.TidT _      -> ()
        | Expr.AddrT _     -> ()                      (* no need to look for firstlock, every  firstlock has a var *)
        | Expr.CellT _     -> ()
        | Expr.SetThT _    -> numtid := !numtid + 1   (* the witness of st1 != st2 *)
        | Expr.SetElemT _  -> numelem := !numelem + 1 (* the witness of se1 != se2 *)
        | Expr.PathT _     -> numaddr := !numaddr + 2 (* the witnesses of p1 != p2 *)
        | Expr.MemT _      -> ()
        | Expr.LevelT _    -> ()
        | Expr.VarUpdate _ -> () in                (* ALE: Not sure if OK *)
      let process (lit:Expr.literal) =
        match lit with
        | F.Atom(Expr.InEq(x,y)) -> process_ineq(x,y)
        | F.Atom(_) -> ()
        | F.NegAtom a ->
            begin
              match a with
              | Expr.Append _       -> numaddr := !numaddr + 2 (* witness of either p1 intersect p2, or (p1;p2) is different from p3 *)
              | Expr.Reach _        -> numaddr := !numaddr + 2 (* witness of p1!=p2 *)
              | Expr.OrderList _    -> numelem := !numelem + 2 (* witnesses for not ordered list *)
              | Expr.In _           -> ()
              | Expr.SubsetEq _     -> numaddr := !numaddr + 1 (* witness of s1 \not\sub s2 *)
              | Expr.InTh _         -> ()
              | Expr.SubsetEqTh _   -> numtid := !numtid + 1 (* witness of st1 \not\sub st2 *)
              | Expr.InElem _       -> ()
              | Expr.SubsetEqElem _ -> numelem := !numelem + 1 (* witness of se1 \not\sub se2 *)
              | Expr.Less _         -> ()
              | Expr.Greater _      -> ()
              | Expr.LessEq _       -> ()
              | Expr.GreaterEq _    -> ()
              | Expr.LessElem _     -> () (* Not sure *)
              | Expr.GreaterElem _  -> () (* Not sure *)
              | Expr.Eq(x,y)        -> process_ineq (x,y)
              | Expr.InEq _         -> ()
              | Expr.BoolVar _      -> ()
              | Expr.PC _           -> ()
              | Expr.PCUpdate _     -> ()
              | Expr.PCRange _      -> ()
            end
      in
        match expr with
        | F.TrueConj  -> MS.create_with [(MS.Addr, 1); (MS.Tid, 1);
                                         (MS.Elem, 1); (MS.Level, 1)]
        | F.FalseConj -> MS.create_with [(MS.Addr, 1); (MS.Tid, 1);
                                         (MS.Elem, 1); (MS.Level, 1)]             
        | F.Conj l    -> (List.iter process l;
                          MS.create_with
                            [(MS.Addr, !numaddr); (MS.Tid, !numtid);
                             (MS.Elem, !numelem); (MS.Level, !numlevel)])


    let compute_max_cut_off (conj_list:Expr.conjunctive_formula list)
          : MS.t =
      let ms = ModelSize.create () in
      List.iter (fun e ->
        let e_cut_off = cut_off_normalized e in
        MS.max_of ms e_cut_off
      ) conj_list;
      ms


    (* I must also count the equalities!!! *)


    let union_ineq_cutoff_pol (info:union_info) ((x,y):(Expr.term * Expr.term)) : union_info =
      match x with
        Expr.VarT _      -> info (* nothing, y must be a VarT as well *)
      | Expr.SetT _      -> union_count_addr info (Expr.InEq(x,y)) (* the witness of s1 != s2 *)
      | Expr.ElemT _     -> info
      | Expr.TidT _     -> info
      | Expr.AddrT _     -> info (* no need to look for firstlock, every firstlock has a var *)
      | Expr.CellT _     -> (* ALE: I added this *)
                              union_count_elem (union_count_tid info (Expr.InEq(x,y))) (Expr.InEq(x,y));
                              (* an element and a tid identifier witness of c1 != c2 *)
      | Expr.SetThT _    -> union_count_tid info (Expr.InEq(x,y)) (* the witness of st1 != st2 *)
      | Expr.SetElemT _  -> union_count_elem info (Expr.InEq(x,y)) (* the witness of se1 != se2 *)
      | Expr.PathT _     -> union_count_addr info (Expr.InEq(x,y)) (* the witnesses of p1 != p2 *)
      | Expr.MemT _      -> info
      | Expr.LevelT _    -> info
      | Expr.VarUpdate _ -> info (* ALE: Not sure if OK *)


    let union_atom_cutoff_pol (pol:Polarity.t) (info:union_info) (a:Expr.atom) : union_info =
      match a with
        Expr.Append _       -> if Polarity.is_pos pol then info else union_count_addr info a
      | Expr.Reach _        -> info (* if pol = Pos then info else union_count_addr info a *)
      | Expr.OrderList _    -> if Polarity.is_pos pol then info else union_count_addr (union_count_elem info a) a
      | Expr.In      _      -> info
      | Expr.SubsetEq _     -> if Polarity.is_pos pol then info else union_count_addr info a
      | Expr.InTh _         -> info
      | Expr.SubsetEqTh _   -> if Polarity.is_pos pol then info else union_count_tid info a
      | Expr.InElem _       -> info
      | Expr.SubsetEqElem _ -> if Polarity.is_pos pol then info else union_count_elem info a
      | Expr.Less _         -> info
      | Expr.Greater _      -> info
      | Expr.LessEq _       -> info
      | Expr.GreaterEq _    -> info
      | Expr.LessElem _     -> info (*union_count_elem info a*)
      | Expr.GreaterElem _  -> info (*union_count_elem info a*)
      | Expr.Eq e           -> if Polarity.is_pos pol then info else union_ineq_cutoff_pol info e
      | Expr.InEq e         -> if Polarity.is_neg pol then info else union_ineq_cutoff_pol info e
      | Expr.BoolVar _      -> info
      | Expr.PC _           -> info
      | Expr.PCUpdate _     -> info
      | Expr.PCRange _      -> info


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
      | F.Iff (f1,f2)     -> apply_cut Polarity.Both (apply_cut Polarity.Both info f1) f2


    let union_formula_cutoff (info:union_info) (phi:Expr.formula) : union_info =
      union_formula_cutoff_pol Polarity.Pos info phi


    let try_pseudo_dnf_union_formula_cutoff (info:union_info) (phi:Expr.formula) : MS.t =
      verbl _LONG_INFO "TRYING PSEUDO DNF\n";
      let split = List.map F.to_disj_list (F.to_conj_list phi) in
      let (atomics,disjs) = List.partition (fun xs -> List.length xs <= 1) split in
      let others_problematic =
        List.fold_left (fun i xs ->
          match xs with
          | atom_phi::_ -> let info = union_model_size
                             (union_formula_cutoff_pol Polarity.Pos new_union_count (atom_phi))
                           in
                             i + (MS.get info MS.Addr)
          | _           -> i
        ) 0 atomics in
      if List.length disjs = 1 && others_problematic = 0 then begin
        let ms = ModelSize.create () in
        List.iter (fun aphi ->
          let this_info = union_model_size (union_formula_cutoff_pol
            Polarity.Pos new_union_count aphi) in
          MS.max_of ms this_info
        ) (List.hd disjs);
        ms
      end else
        let _ = verbl _LONG_INFO "WE DON'T HAVE A CANDIDATE: %s\n" (Expr.formula_to_str phi) in
        union_model_size (union_formula_cutoff_pol Polarity.Pos info phi)


    (* Union SMP *)
    let compute_max_cut_off_with_union (phi:Expr.formula) : MS.t =
      let vars = Expr.get_varset_from_formula phi in
      let addrvars = V.varset_of_sort vars Expr.Addr in
      let interesting_addrvars = VarSet.fold (fun v s ->
                                   if (not (V.is_fresh v)) || TSLK.variable_is_smp_interesting v then
                                     (Expr.variable_mark_smp_interesting v true; VarSet.add v s)
                                   else
                                     s
                                 ) addrvars VarSet.empty in
      verbl _LONG_INFO "CANDIDATE Interesting addresses:%s\n"
        (VarSet.fold (fun v str -> str ^ (Expr.V.to_str v) ^ ";") 
      interesting_addrvars "");
      let vartid_num  = VarSet.cardinal (V.varset_of_sort vars Expr.Tid) in
      let varaddr_num = VarSet.cardinal interesting_addrvars in
      let varelem_num = VarSet.cardinal (V.varset_of_sort vars Expr.Elem) in
      let info = try_pseudo_dnf_union_formula_cutoff new_union_count phi in

      let num_levels = Expr.k in
      let num_addrs = (* 1 + *)                               (* null (is already unique) *)
                      varaddr_num +                           (* Address variables  *)
(*                      varcell_num * num_levels              + (* Cell next pointers *) *)
(*                      varaddr_num * varmem_num * num_levels + (* Cell next pointers *) *)
                      (MS.get info MS.Addr)                     (* Special literals   *) in
      let num_tids = 1 + vartid_num + (MS.get info MS.Tid) in
(*                    1 +                                      (* No thread          *)
                       vartid_num +                             (* Tid variables     *)
                       varcell_num * num_levels                 (* Cell locks         *) in
(*                     varmem_num * num_addrs * num_levels      (* Cell locks         *) in *)
*)
      let num_elems = max 1 (varelem_num + (MS.get info MS.Elem))
(*                    varelem_num                             (* Elem variables     *) *)
(*                    varmem_num * num_addrs                  (* Cell data          *) *)
      in
        MS.create_with [(MS.Level, num_levels); (MS.Addr, num_addrs);
                        (MS.Tid, num_tids); (MS.Elem, num_elems)]


    (* Pruning SMP *)
    let prune_eq (x:Expr.term) (y:Expr.term) : (Expr.term * Expr.term) option =
      match x with
          Expr.VarT _      -> None (* nothing, y must be a VarT as well *)
        | Expr.SetT _      -> Some (x,y) (* the witness of s1 != s2 *)
        | Expr.ElemT _     -> Some (x,y)
        | Expr.TidT _      -> Some (x,y)
        | Expr.AddrT _     -> Some (x,y) (* For mem[a].next literals *)
        | Expr.CellT _     -> None
        | Expr.SetThT _    -> Some (x,y) (* the witness of st1 != st2 *)
        | Expr.SetElemT _  -> Some (x,y) (* the witness of se1 != se2 *)
        | Expr.PathT _     -> Some (x,y) (* the witnesses of p1 != p2 *)
        | Expr.MemT _      -> Some (x,y)
        | Expr.LevelT _    -> Some (x,y)
        | Expr.VarUpdate _ -> assert(false) (* ALE: Not sure if OK *)


    let prune_atom (a:Expr.atom) : Expr.atom option =
      match a with
        Expr.Append _       -> Some a
      | Expr.Reach _        -> Some a
      | Expr.OrderList _    -> Some a
      | Expr.In _           -> Some a
      | Expr.SubsetEq _     -> Some a
      | Expr.InTh _         -> Some a
      | Expr.SubsetEqTh _   -> Some a
      | Expr.InElem _       -> Some a
      | Expr.SubsetEqElem _ -> Some a
      | Expr.Less _         -> None
      | Expr.Greater _      -> None
      | Expr.LessEq _       -> None
      | Expr.GreaterEq _    -> None
      | Expr.LessElem _     -> Some a
      | Expr.GreaterElem _  -> Some a
      | Expr.Eq (x,y)       -> Option.lift (fun (x',y') -> Expr.Eq (x',y')) (prune_eq x y)
      | Expr.InEq (x,y)     -> Option.lift (fun (x',y') -> Expr.InEq (x',y')) (prune_eq x y)
      | Expr.BoolVar _      -> None
      | Expr.PC _           -> None
      | Expr.PCUpdate _     -> None
      | Expr.PCRange _      -> None


    let compute_max_cut_off_with_pruning (phi:Expr.formula) : MS.t =
      let pruned_phi = Option.default F.True (F.prune_formula prune_atom (F.nnf phi)) in
      let new_dnf = List.map F.cleanup_conj (F.dnf pruned_phi) in
        compute_max_cut_off (new_dnf)


    let cut_off (strat:Smp.cutoff_strategy_t)
                (opt:Smp.cutoff_options_t)
                (f:Expr.formula) : MS.t =
(*      LOG "Strategy: %s\n" (Smp.strategy_to_str strat) LEVEL DEBUG; *)
      options := opt;
      let model_s = match strat with
                    | Smp.Dnf     -> compute_max_cut_off (F.dnf f)
                    | Smp.Union   -> compute_max_cut_off_with_union f
                    | Smp.Pruning -> compute_max_cut_off_with_pruning f
      in
      verbl _LONG_INFO "SMP TSLK DOMAINS: %s" (MS.to_str model_s);
      model_s
  end
