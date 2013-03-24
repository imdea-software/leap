
open TSLExpression
open LeapLib
open LeapVerbose

module Arr = Arrangements
module GenSet = LeapGenericSet
module TslExp = TSLExpression
module type TslkExp = TSLKExpression.S



let solver_impl = ref ""


let choose (s:string) : unit =
  solver_impl := s


let comp_model : bool ref = ref false
(* Should we compute a model in case of courter example? *)

let cutoff_opt : Smp.cutoff_options_t = Smp.opt_empty()
(* The structure where we store the options for cutoff *)


let gen_fresh_addr_var (vs:TslExp.VarSet.t) : TslExp.variable =
  let rec find (n:int) : TslExp.variable =
    let v_cand_id = "fresh_addr_" ^ (string_of_int n) in
    let v_cand = TslExp.build_var v_cand_id TslExp.Int false None None in
      if TslExp.VarSet.mem v_cand vs then find (n+1) else v_cand
  in
    find 0


let sanitize (cf:TslExp.conjunctive_formula) : TslExp.conjunctive_formula =
  let find_candidates (ls:TslExp.literal list)
        : (TslExp.VarSet.t * TslExp.VarSet.t)  =
    List.fold_left (fun (cs,ss) l ->
      match l with
      | Atom(Eq(_,AddrArrayT(AddrArrayUp(_,VarInt v,_)))) ->
        (TslExp.VarSet.add v cs, ss)
      | Atom(Eq(IntT(VarInt _), IntT(IntAdd (VarInt v, IntVal 1)))) ->
        (cs, TslExp.VarSet.add v ss)
      | Atom(Eq(IntT(IntAdd (VarInt v, IntVal 1)), IntT (VarInt _))) ->
        (cs, TslExp.VarSet.add v ss)
      | _ -> (cs, ss)
    ) (TslExp.VarSet.empty, TslExp.VarSet.empty) ls
  in
  match cf with
  | TslExp.FalseConj -> cf
  | TslExp.TrueConj  -> cf
  | TslExp.Conj ls   -> let vars = TslExp.varset_from_conj cf in
                        let (cs,ss) = find_candidates ls in
                        let needs_sanit = TslExp.VarSet.diff cs ss in
                        let ls' = TslExp.VarSet.fold (fun v xs ->
                                    let v_new = VarInt (gen_fresh_addr_var vars) in
                                    (Atom(Eq(IntT v_new, IntT(IntAdd(VarInt v, IntVal 1))))) :: ls
                                  ) needs_sanit ls
                        in
                          TslExp.Conj ls'


let guess_arrangements_by_brute_force (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula list =
  LOG "Entering guess_arrangements..." LEVEL TRACE;
  let rec cons_var_eq_class (vs:TslExp.variable list) : TslExp.literal list =
    match vs with
    | v1::v2::xs -> Atom(Eq(IntT (VarInt v1), IntT (VarInt v2))) :: cons_var_eq_class (v2::xs)
    | _          -> []
  in
  let rec cons_var_ords (arr:TslExp.variable list list) : TslExp.literal list =
    match arr with
    | xs::ys::zs -> Atom(Less(VarInt(List.hd xs),
                              VarInt(List.hd ys))) :: cons_var_ords (ys::zs)
    | _          -> []
  in
  match cf with
  | TslExp.FalseConj -> []
  | TslExp.TrueConj  -> []
  | TslExp.Conj ls   -> verb "**** TSL Solver. Computing level vars from: %s\n"
                              (TslExp.conjunctive_formula_to_str cf);
                        let level_vars = TslExp.varset_of_sort_from_conj cf TslExp.Int in
                        verb "**** TSL Solver. Extracted level vars: %s\n"
                              (String.concat ", " $
                                TslExp.VarSet.fold (fun v xs ->
                                  (TslExp.variable_to_str v) :: xs
                                ) level_vars []);
                        verb "**** TSL Solver. Computing partitions...\n";
                        let parts = Partition.gen_partitions
                                      (TslExp.VarSet.elements level_vars) [] in
                        verb "**** TSL Solver. Computing equalities...\n";
                        let eqs = List.fold_left (fun xs p ->
                                    (Partition.to_list p) :: xs
                                  ) [] parts in
                        verb "**** TSL Solver. Level vars: %i\n"
                              (TslExp.VarSet.cardinal level_vars);
                        verb "**** TSL Solver. Computing arrangements...\n";
                        let arrgs = List.fold_left (fun xs eq_c ->
                                      (LeapLib.comb eq_c (List.length eq_c)) @ xs
                                    ) [] eqs in
                        verb "**** TSL Solver. Computing level arrangements...\n";
                        let lv_arrs = List.fold_left (fun xs arr ->
                                        let eqs = List.fold_left (fun ys eq_c ->
                                                    (cons_var_eq_class eq_c) @ ys
                                                  ) [] arr in
                                        let ords = cons_var_ords arr
                                        in
                                          (TslExp.Conj (eqs @ ords)) :: xs
                                      ) [] arrgs
                        in
                          lv_arrs


let guess_arrangements (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula list =
  let rec cons_eq_class (is:TslExp.integer list) : TslExp.literal list =
    match is with
    | i1::i2::xs -> Atom(Eq(IntT i1, IntT i2)) :: cons_eq_class (i2::xs)
    | _          -> []
  in
  let rec cons_ords (arr:TslExp.integer list list) : TslExp.literal list =
    match arr with
    | xs::ys::zs -> Atom(Less(List.hd xs,
                              List.hd ys)) :: cons_ords (ys::zs)
    | _          -> []
  in
  let arr = Arr.empty() in
    match cf with
    | TslExp.FalseConj -> []
    | TslExp.TrueConj  -> []
    | TslExp.Conj ls   -> begin
                            let level_vars = TslExp.varset_instances_of_sort_from_conj cf (TslExp.Int) in
                            Printf.printf "THIS IS THE CONJUNCTION TO BE ANALYZED:\n%s\n" (TslExp.conjunctive_formula_to_str cf);
(*
                            let level_vars = TslExp.VarSet.fold (fun v s ->
                                               TslExp.VarSet.add (TslExp.unlocalize_variable v) s
                                             ) original_vars TslExp.VarSet.empty in
*)
                            TslExp.VarSet.iter (fun v -> Arr.add_elem arr (TslExp.VarInt v)) level_vars;
                            List.iter (fun l ->
                              match l with
                              | TslExp.Atom(TslExp.Less(i1,i2)) -> Arr.add_order arr i1 i2
                              | TslExp.Atom(TslExp.Greater(i1,i2)) -> Arr.add_order arr i2 i1
                              | TslExp.Atom(TslExp.Eq(IntT i1,IntT i2)) -> Arr.add_eq arr i1 i2
                              | TslExp.Atom(TslExp.InEq(IntT i1,IntT i2)) -> Arr.add_ineq arr i1 i2
                              | TslExp.NegAtom(TslExp.LessEq(i1,i2)) -> Arr.add_order arr i2 i1
                              | TslExp.NegAtom(TslExp.GreaterEq(i1,i2)) -> Arr.add_order arr i1 i2
                              | TslExp.NegAtom(TslExp.Eq(IntT i1,IntT i2)) -> Arr.add_ineq arr i1 i2
                              | TslExp.NegAtom(TslExp.InEq(IntT i1,IntT i2)) -> Arr.add_eq arr i1 i2
                              | _ -> ()
                            ) ls;
                            GenSet.fold (fun s_elem xs ->
                              let eqs = List.fold_left (fun ys eq_c ->
                                          (cons_eq_class eq_c) @ ys
                                        ) [] s_elem in
                              let ords = cons_ords s_elem in
                                (TslExp.Conj (eqs @ ords)) :: xs
                            ) (Arr.gen_arrs arr) []
                          end


let split (cf:TslExp.conjunctive_formula)
      : TslExp.conjunctive_formula * TslExp.conjunctive_formula =
  match cf with
  | TslExp.TrueConj  -> (TslExp.TrueConj,  TslExp.TrueConj)
  | TslExp.FalseConj -> (TslExp.FalseConj, TslExp.FalseConj)
  | TslExp.Conj cf   ->
      let (pa,nc) = List.fold_left (fun (pas,ncs) l ->
                      match l with
                        (* l = q *)
                      | Atom(Eq(IntT(VarInt _),IntT(IntVal _)))
                      | Atom(Eq(IntT(IntVal _),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT(IntVal _)))
                      | NegAtom(InEq(IntT(IntVal _),IntT(VarInt _))) -> (l::pas,ncs)
                        (* l1 = l2 *)
                      | Atom(InEq(IntT(VarInt _),IntT(VarInt _)))
                      | NegAtom(Eq(IntT(VarInt _),IntT(VarInt _)))
                        (* l1 = l2 + 1*)
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | Atom(Eq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | Atom(Eq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | Atom(Eq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (VarInt _, IntVal 1))))
                      | NegAtom(InEq(IntT(VarInt _),IntT (IntAdd (IntVal 1, VarInt _))))
                      | NegAtom(InEq(IntT(IntAdd(VarInt _,IntVal 1)),IntT(VarInt _)))
                      | NegAtom(InEq(IntT(IntAdd(IntVal 1,VarInt _)),IntT(VarInt _)))
                        (* l1 < l2 *) (* l1 <= l2 should not appear here after normalization *)
                      | Atom(Less(VarInt _,VarInt _))
                      | Atom(Greater(VarInt _,VarInt _))
                      | NegAtom(LessEq(VarInt _,VarInt _))
                      | NegAtom(GreaterEq(VarInt _,VarInt _)) -> (l::pas,l::ncs)
                      | _ -> (pas,l::ncs)
                    ) ([],[]) cf
      in
        (TslExp.Conj pa, TslExp.Conj nc)


module TranslateTsl (TslkExp : TSLKExpression.S) =
  struct

    module TslkInterf = TSLKInterface.Make(TslkExp)

    let tid_tsl_to_tslk (t:TslExp.tid) : TslkExp.tid =
      TslkInterf.tid_to_tslk_tid(TSLInterface.tid_to_expr_tid t)

    let term_tsl_to_term (t:TslExp.term) : TslkExp.term =
      TslkInterf.term_to_tslk_term(TSLInterface.term_to_expr_term t)

    let set_tsl_to_tslk (s:TslExp.set) : TslkExp.set =
      TslkInterf.set_to_tslk_set(TSLInterface.set_to_expr_set s)

    let elem_tsl_to_tslk (e:TslExp.elem) : TslkExp.elem =
      TslkInterf.elem_to_tslk_elem(TSLInterface.elem_to_expr_elem e)

    let addr_tsl_to_tslk (a:TslExp.addr) : TslkExp.addr =
      TslkInterf.addr_to_tslk_addr(TSLInterface.addr_to_expr_addr a)

    let cell_tsl_to_tslk (c:TslExp.cell) : TslkExp.cell =
      TslkInterf.cell_to_tslk_cell(TSLInterface.cell_to_expr_cell c)

    let setth_tsl_to_tslk (s:TslExp.setth) : TslkExp.setth =
      TslkInterf.setth_to_tslk_setth(TSLInterface.setth_to_expr_setth s)

    let setelem_tsl_to_tslk (s:TslExp.setelem) : TslkExp.setelem =
      TslkInterf.setelem_to_tslk_setelem(TSLInterface.setelem_to_expr_setelem s)

    let path_tsl_to_tslk (p:TslExp.path) : TslkExp.path =
      TslkInterf.path_to_tslk_path(TSLInterface.path_to_expr_path p)

    let mem_tsl_to_tslk (m:TslExp.mem) : TslkExp.mem =
      TslkInterf.mem_to_tslk_mem(TSLInterface.mem_to_expr_mem m)

    let int_tsl_to_tslk (i:TslExp.integer) : TslkExp.level =
      TslkInterf.int_to_tslk_level(TSLInterface.int_to_expr_int i)

    let literal_tsl_to_tslk (l:TslExp.literal) : TslkExp.literal =
      TslkInterf.literal_to_tslk_literal(TSLInterface.literal_to_expr_literal l)

    let gen_varlist (base:string) (s:TslkExp.sort)
                    (i:int) (j:int) : TslkExp.variable list =
      let xs = ref [] in
      for n = i to j do
        let id = base ^ (string_of_int n) in
        let v = TslkExp.build_var id s false None None in
        xs := v::(!xs)
      done;
      List.rev !xs


    let gen_addr_list (aa:TslExp.addrarr) (i:int) (j:int) : TslkExp.addr list =
      let vs = gen_varlist (TslExp.addrarr_to_str aa) TslkExp.Addr i j in
      List.map (fun v -> TslkExp.VarAddr v) vs


    let gen_tid_list (tt:TslExp.tidarr) (i:int) (j:int) : TslkExp.tid list =
      let vs = gen_varlist (TslExp.tidarr_to_str tt) TslkExp.Thid i j in
      List.map (fun v -> TslkExp.VarTh v) vs
    
    let rec trans_literal (l:TslExp.literal) : TslkExp.formula =
      verb "**** TSL Solver. Literal to be translated: %s\n"
            (TslExp.literal_to_str l);
      match l with
      (* c = mkcell(e,k,A,l) *)
      | Atom(Eq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | Atom(Eq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c)))
      | NegAtom(InEq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | NegAtom(InEq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c))) ->
          let c' = cell_tsl_to_tslk (VarCell c) in
          let e' = elem_tsl_to_tslk e in
          let aa' = gen_addr_list aa 0 (TslkExp.k - 1) in
          let tt' = gen_tid_list tt 0 (TslkExp.k - 1) in
            TslkExp.eq_cell (c') (TslkExp.MkCell(e',aa',tt'))
      (* c != mkcell(e,k,A,l) *)
      | NegAtom(Eq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | NegAtom(Eq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c)))
      | Atom(InEq(CellT (VarCell c),CellT(MkCell(e,aa,tt,i))))
      | Atom(InEq(CellT(MkCell(e,aa,tt,i)),CellT (VarCell c))) ->
          TslkExp.Not (trans_literal (Atom(Eq(CellT(VarCell c), CellT(MkCell(e,aa,tt,i))))))
      (* a = A[i] *)
      | Atom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | Atom(Eq(AddrT (AddrArrRd (aa,i)), AddrT a))
      | NegAtom(InEq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | NegAtom(InEq(AddrT (AddrArrRd (aa,i)), AddrT a)) ->
          let a' = addr_tsl_to_tslk a in
          let aa' = gen_addr_list aa 0 (TslkExp.k - 1) in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          TslkExp.conj_list (!xs)
      (* a != A[i] *)
      | NegAtom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | NegAtom(Eq(AddrT (AddrArrRd (aa,i)), AddrT a))
      | Atom(InEq(AddrT a, AddrT (AddrArrRd (aa,i))))
      | Atom(InEq(AddrT (AddrArrRd (aa,i)), AddrT a)) ->
          TslkExp.Not (trans_literal (Atom(Eq(AddrT a, AddrT (AddrArrRd (aa,i))))))
      (* t = A[i] *)
      | Atom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | Atom(Eq(ThidT (ThidArrRd (tt,i)), ThidT t))
      | NegAtom(InEq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | NegAtom(InEq(ThidT (ThidArrRd (tt,i)), ThidT t)) ->
          let t' = tid_tsl_to_tslk t in
          let tt' = gen_tid_list tt 0 (TslkExp.k - 1) in
          let i' = int_tsl_to_tslk i in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_tid t' (List.nth tt' n))) :: (!xs)
          done;
          TslkExp.conj_list (!xs)
      (* t != A[i] *)
      | NegAtom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | NegAtom(Eq(ThidT (ThidArrRd (tt,i)), ThidT t))
      | Atom(InEq(ThidT t, ThidT (ThidArrRd (tt,i))))
      | Atom(InEq(ThidT (ThidArrRd (tt,i)), ThidT t)) ->
          TslkExp.Not (trans_literal (Atom(Eq(ThidT t, ThidT (ThidArrRd (tt,i))))))
      (* B = A {l <- a} *)
      | Atom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | Atom(Eq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb))
      | NegAtom(InEq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | NegAtom(InEq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb)) ->
          let a' = addr_tsl_to_tslk a in
          let i' = int_tsl_to_tslk i in
          let aa' = gen_addr_list aa 0 (TslkExp.k - 1) in
          let bb' = gen_addr_list bb 0 (TslkExp.k - 1) in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_addr a' (List.nth bb' n))) ::
                  (TslkExp.Implies
                    (TslkExp.ineq_level i' n',
                     TslkExp.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                  (!xs)
          done;
          TslkExp.conj_list (!xs)
      (* B != A {l <- a} *)
      | NegAtom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | NegAtom(Eq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb))
      | Atom(InEq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))
      | Atom(InEq(AddrArrayT (AddrArrayUp(aa,i,a)), AddrArrayT bb)) ->
          TslkExp.Not (trans_literal (Atom(Eq(AddrArrayT bb, AddrArrayT (AddrArrayUp(aa,i,a))))))
      (* U = T {l <- t} *)
      | Atom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | Atom(Eq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu))
      | NegAtom(InEq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | NegAtom(InEq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu)) ->
          let t' = tid_tsl_to_tslk t in
          let i' = int_tsl_to_tslk i in
          let tt' = gen_tid_list tt 0 (TslkExp.k - 1) in
          let uu' = gen_tid_list uu 0 (TslkExp.k - 1) in
          let xs = ref [] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Implies
                    (TslkExp.eq_level i' n',
                     TslkExp.eq_tid t' (List.nth uu' n))) ::
                  (TslkExp.Implies
                    (TslkExp.ineq_level i' n',
                     TslkExp.eq_tid (List.nth tt' n) (List.nth uu' n))) ::
                  (!xs)
          done;
          TslkExp.conj_list (!xs)
      (* U != T {l <- t} *)
      | NegAtom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | NegAtom(Eq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu))
      | Atom(InEq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))
      | Atom(InEq(TidArrayT (TidArrayUp(tt,i,t)), TidArrayT uu)) ->
          TslkExp.Not (trans_literal (Atom(Eq(TidArrayT uu, TidArrayT (TidArrayUp(tt,i,t))))))
      (* Skiplist (m,s,i,s1,s2) *)
      | Atom(Skiplist(m,s,i,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in
          let xs = ref
                    [TslkExp.Literal(TslkExp.Atom(
                      TslkExp.OrderList(m',a1',a2')));
                     TslkExp.eq_set
                      (s')
                      (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelVal 0)))] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.eq_addr (TslkExp.NextAt(TslkExp.CellAt(m',a2'),n'))

                                   (TslkExp.Null)) :: (!xs)
          done;
          for n = 0 to (TslkExp.k - 2) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Literal(TslkExp.Atom(TslkExp.SubsetEq(
                    TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelSucc n')),
                    TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',n')))))) :: (!xs)
          done;
          TslkExp.conj_list (!xs)
      (* ~ Skiplist(m,s,i,a1,a2) *)
      | NegAtom(Skiplist(m,s,i,a1,a2)) ->
          let m' = mem_tsl_to_tslk m in
          let s' = set_tsl_to_tslk s in
          let a1' = addr_tsl_to_tslk a1 in
          let a2' = addr_tsl_to_tslk a2 in


          let xs = ref
                    [TslkExp.Literal(TslkExp.NegAtom(
                      TslkExp.OrderList(m',a1',a2')));
                     TslkExp.ineq_set
                      (s')
                      (TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelVal 0)))] in
          for n = 0 to (TslkExp.k - 1) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.ineq_addr (TslkExp.NextAt(TslkExp.CellAt(m',a2'),n'))
                                   (TslkExp.Null)) :: (!xs)
          done;
          for n = 0 to (TslkExp.k - 2) do
            let n' = TslkExp.LevelVal n in
            xs := (TslkExp.Literal(TslkExp.NegAtom(TslkExp.SubsetEq(
                    TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',TslkExp.LevelSucc n')),
                    TslkExp.PathToSet(TslkExp.GetPathAt(m',a1',a2',n')))))) :: (!xs)
          done;
          TslkExp.disj_list (!xs)
      | _ -> TslkExp.Literal (literal_tsl_to_tslk l)


    let to_tslk (tsl_ls:TslExp.literal list) : TslkExp.formula =
      let tslk_ps = List.map trans_literal tsl_ls in
      TslkExp.conj_list tslk_ps
  end



let check_sat_by_cases (lines:int)
                       (stac:Tactics.solve_tactic_t option)
                       (co : Smp.cutoff_strategy)
                       (cases:(TslExp.conjunctive_formula  *     (* PA formula *)
                               TslExp.conjunctive_formula) list) (* NC formula *)
      : (bool * int * int) =

  (* PA satisfiability check function *)
  let check_pa (cf:TslExp.conjunctive_formula) : bool =
    match cf with
    | TslExp.TrueConj  -> (verb "**** check_pa: true\n"; true)
    | TslExp.FalseConj -> (verb "**** check_pa: false\n"; false)
    | TslExp.Conj ls   ->
        verb "**** check_pa: conjunction of literals\n";
        let numSolv_id = BackendSolvers.Yices.identifier in
        let module NumSol = (val NumSolver.choose numSolv_id : NumSolver.S) in

        verb "A0\n";
        let a1 = (TslExp.from_conjformula_to_formula
                            cf) in
        verb "A1\n";
        let a2 = (TSLInterface.formula_to_expr_formula a1) in
        verb "A2\n";
        verb "FORMULA TO INT:\n%s\n" (Expression.formula_to_str a2);
        let a3 = NumExpression.formula_to_int_formula a2 in
        verb "A3\n";
        let phi_num = a3
(*
        let phi_num = NumExpression.formula_to_int_formula
                        (TSLInterface.formula_to_expr_formula
                          (TslExp.from_conjformula_to_formula
                            cf))
*)
        in
        verb "**** TSL Solver numeric formula: %s\n"
                  (TslExp.conjunctive_formula_to_str cf);
        verb "**** TSL Solver will pass numeric formula: %s\n"
                  (NumExpression.int_formula_to_string phi_num);
        NumSol.is_sat phi_num in


  (* NC satisfiability check function *)
  let check_nc (cf:TslExp.conjunctive_formula) : bool =
    match cf with
    | TslExp.TrueConj  -> true
    | TslExp.FalseConj -> false
    | TslExp.Conj ls ->
        let l_vs = varset_of_sort_from_conj cf Int in
        let k = VarSet.cardinal l_vs in
        let module TslkSol = (val TslkSolver.choose "Z3" k
  (*
        let module TslkSol = (val TslkSolver.choose !solver_impl k
  *)
                                         : TslkSolver.S) in
        let module Trans = TranslateTsl (TslkSol.TslkExp) in
        verb "**** TSL Solver, about to translate TSL to TSLK...\n";
        let phi_tslk = Trans.to_tslk ls in
        verb "**** TSL Solver, TSL to TSLK translation done...\n";
        TslkSol.is_sat lines stac co phi_tslk in


  (* General satisfiability function *)
  let rec check (pa:TslExp.conjunctive_formula)
                (nc:TslExp.conjunctive_formula)
                (arrgs:TslExp.conjunctive_formula list) =
    verb "**** TSL Solver. PA: %s\n" (TslExp.conjunctive_formula_to_str pa);
    verb "**** TSL Solver. NC: %s\n" (TslExp.conjunctive_formula_to_str nc);
    match arrgs with
    | [] -> false
    | alpha::xs ->
        (* Check PA /\ alpha satisfiability *)
        let pa_sat = check_pa (TslExp.combine_conj_formula pa alpha) in
        verb "**** TSL Solver, PA sat?: %b\n" pa_sat;
        if pa_sat then
          (* Check NC /\ alpha satisfiability *)
          let _ = verb "**** TSL Solver will combine NC and arrangements.\n" in
          let nc_sat = check_nc (TslExp.combine_conj_formula nc alpha) in
          if nc_sat then true else check pa nc xs
        else
          check pa nc xs in

  (* Main call *)
  let tslk_calls = ref 0 in
  let rec check_aux cs =
    verb "**** TSL Solver: %i cases\n%s\n" (List.length cs)
            (String.concat "\n"
              (List.map (fun (pa,nc) ->
                Printf.sprintf "PA: %s\nNC: %s\n--------\n"
                  (TslExp.conjunctive_formula_to_str pa)
                  (TslExp.conjunctive_formula_to_str nc)) cs));
    match cs with
    | []          -> (false, 1, !tslk_calls)
    | (pa,nc)::xs -> begin
                       verb "**** TSL Solver: will guess arrangements...\n";
                       let arrgs = guess_arrangements (TslExp.combine_conj_formula pa nc) in
                       verb "**** TSL Solver: arrangements guessed: %i...\n" (List.length arrgs);
                       match arrgs with
                       | [] -> (* No arrangements guessed, ie. less than 2 level variables.
                                  Only need to check NC *)
                               (check_nc nc, 1, !tslk_calls)
                       | _  -> (* Some arrangement guessed. Full check required *)
                               if check pa nc arrgs then
                                 (true, 1, !tslk_calls)
                               else
                                 check_aux xs
                     end
  in
    check_aux cases


let is_sat_plus_info (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy)
           (phi : TslExp.formula) : (bool * int * int) =
  (* 0. Normalize the formula and rewrite it in DNF *)
  verb "**** Will normalize TSL formula...\n";
  let phi_norm = TslExp.normalize phi in
  verb "**** Original TSL formula:\n%s\n" (TslExp.formula_to_str phi);
  verb "**** Normalized TSL formula:\n%s\n" (TslExp.formula_to_str phi_norm);
  verb "**** Will do DNF on TSL formula...\n";
  let phi_dnf = TslExp.dnf phi_norm in
  (* 1. Sanitize the formula *)
  verb "**** Will sanitize TSL formula...\n";
  let phi_san = List.map sanitize phi_dnf in
  (* 2. Split each conjunction into PA y NC *)
  verb "**** Will split TSL formula in NC and PA...\n";
  let splits = List.map split phi_san in
  (* 3. Call the solver for each possible case *)
  verb "**** Will check TSL formula satisfiability...\n";
  let (sat,tsl_calls,tslk_calls) = check_sat_by_cases lines stac co splits
  in
    (sat, tsl_calls, tslk_calls)


let is_sat (lines : int)
           (stac:Tactics.solve_tactic_t option)
           (co : Smp.cutoff_strategy)
           (phi : TslExp.formula) : bool =
  (* Here goes the code for satisfiability from the paper *)
  let (s,_,_) = is_sat_plus_info lines stac co phi in s


let is_valid_plus_info (prog_lines:int)
                       (stac:Tactics.solve_tactic_t option)
                       (co:Smp.cutoff_strategy)
                       (phi:TslExp.formula) : (bool * int * int) =
  let (s,tsl_count,tslk_count) = is_sat_plus_info prog_lines stac co
                                   (TslExp.Not phi) in
    (not s, tsl_count, tslk_count)


let is_valid (prog_lines:int)
             (stac:Tactics.solve_tactic_t option)
             (co:Smp.cutoff_strategy)
             (phi:TslExp.formula) : bool =
  not (is_sat prog_lines stac co phi)


let compute_model (b:bool) : unit =
  let _ = comp_model := b
  in ()
    (* Should I enable which solver? *)
    (* Solver.compute_model b *)
    (* Perhaps I should only set the flag and set activate the compute_model
       on the Solver when it is about to be called in is_sat *)


let model_to_str () : string =
  ""


let print_model () : unit =
  if !comp_model then
    print_endline (model_to_str())
  else
    ()


let set_forget_primed_mem (b:bool) : unit =
  Smp.set_forget_primed_mem cutoff_opt b


let set_group_vars (b:bool) : unit =
  Smp.set_group_vars cutoff_opt b
