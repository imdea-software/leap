(* Full normalization of TSL literals *)

(*
  match l with
  (* e = c.data *)
  | Atom (Eq (e, ElemT (CellData c)))
  | Atom (Eq (ElemT (CellData c), e))
  | NegAtom (InEq (e, ElemT (CellData c)))
  | NegAtom (InEq (ElemT (CellData c), e)) ->
      let e_var = VarElem (gen_if_not_var e Elem) in
      let c_var = VarCell (gen_if_not_var (CellT c) Cell) in
      let aa = gen_fresh_addrarr_var info in
      let tt = gen_fresh_tidarr_var info in
      let i  = gen_fresh_int_var info in
        eq_cell (c_var) (MkCell(e_var,aa,tt,i))
  (* a = c.next[l] *)
  | Atom (Eq (a, AddrT (ArrAt (c,i))))
  | Atom (Eq (AddrT (ArrAt (c,i)), a))
  | NegAtom (InEq (a, AddrT (ArrAt (c,i))))
  | NegAtom (InEq (AddrT (ArrAt (c,i)), a)) ->
      let a_var = gen_if_not_var a Addr in
      let c_var = gen_if_not_var (CellT c) Cell in
      let i_var = gen_if_not_var (IntT i) Int in
      let e  = gen_fresh_elem_var info in
      let aa = gen_fresh_addrarr_var info in
      let tt = gen_fresh_tidarr_var info in
        append_if_diff (CellT (MkCell(e,aa,tt,VarInt i_var))) c_var;
        eq_addr (VarAddr a_var) (AddrArrRd(aa, VarInt i_var))
  (* m1 != m2 *)
  | Atom (InEq (MemT m1, MemT m2))
  | NegAtom (Eq (MemT m1, MemT m2)) ->
      let m1_var = gen_if_not_var (MemT m1) Mem in
      let m2_var = gen_if_not_var (MemT m2) Mem in
      let a  = gen_fresh_addr_var info in
      let c1 = gen_fresh_var info.fresh_gen_info Cell in
      let c2 = gen_fresh_var info.fresh_gen_info Cell in
        append_if_diff (CellT (CellAt (VarMem m1_var, a))) c1;
        append_if_diff (CellT (CellAt (VarMem m2_var, a))) c2;
        ineq_cell (VarCell c1) (VarCell c2)
  (* s1 != s2 *)
  | Atom (InEq (SetT s1, SetT s2))
  | NegAtom (Eq (SetT s1, SetT s2)) ->
      let s1_var = gen_if_not_var (SetT s1) Set in
      let s2_var = gen_if_not_var (SetT s2) Set in
      let s12  = gen_fresh_set_var info in
      let s21  = gen_fresh_set_var info in
      let s3   = gen_fresh_set_var info in
      let s    = gen_fresh_set_var info in
      let sing = gen_fresh_set_var info in
      let a    = gen_fresh_addr_var info in
        conj_list [eq_set (s12) (Setdiff (VarSet s1_var, VarSet s2_var));
                   eq_set (s21) (Setdiff (VarSet s2_var, VarSet s1_var));
                   eq_set (s3) (Union (s12, s21));
                   eq_set (sing) (Singl a);
                   eq_set (s) (Union (s3,sing));
                   eq_set (s) (Union (sing,s))]
  (* s = empty *)
  | Atom (Eq (SetT s, SetT EmptySet))
  | Atom (Eq (SetT EmptySet, SetT s))
  | NegAtom (InEq (SetT s, SetT EmptySet))
  | NegAtom (InEq (SetT EmptySet, SetT s)) ->
      let s_var = gen_if_not_var (SetT s) Set in
      eq_set (VarSet s_var) (Setdiff (VarSet s_var, VarSet s_var))
  (* s3 = s1 cap s2 *)
  | Atom (Eq (SetT s3, SetT (Intr (s1, s2))))
  | Atom (Eq (SetT (Intr (s1, s2)), SetT s3))
  | NegAtom (InEq (SetT s3, SetT (Intr (s1, s2))))
  | NegAtom (InEq (SetT (Intr (s1, s2)), SetT s3)) ->
      let s1_var = gen_if_not_var (SetT s1) Set in
      let s2_var = gen_if_not_var (SetT s2) Set in
      let s3_var = gen_if_not_var (SetT s3) Set in
      let s12 = gen_fresh_set_var info in
      let s21 = gen_fresh_set_var info in
      let su1 = gen_fresh_set_var info in
      let su2 = gen_fresh_set_var info in
        conj_list [eq_set (s12) (Setdiff (VarSet s1_var, VarSet s2_var));
                   eq_set (s21) (Setdiff (VarSet s2_var, VarSet s1_var));
                   eq_set (su1) (Union (VarSet s1_var, VarSet s2_var));
                   eq_set (su2) (Union (s12, s21));
                   eq_set (VarSet s3_var) (Setdiff (su1,su2))]
  (* a in s *)
  | Atom (In (a,s)) ->
      let a_var = gen_if_not_var (AddrT a) Addr in
      let s_var = gen_if_not_var (SetT s) Set in
      let sa = gen_fresh_set_var info in
        conj_list [eq_set (sa) (Singl (VarAddr a_var));
                   eq_set (VarSet s_var) (Union (sa,VarSet s_var))]
  (* not (a in s) *)
  | NegAtom (In (a,s)) ->
      let a_var = gen_if_not_var (AddrT a) Addr in
      let s_var = gen_if_not_var (SetT s) Set in
      let sa = gen_fresh_set_var info in
        let diff_phi = norm_literal info
                          (Atom(InEq(SetT(VarSet s_var),
                                     SetT(Union(sa,VarSet s_var))))) in
        conj_list [eq_set (sa) (Singl (VarAddr a_var));
                   diff_phi]
  (* s1 subset s2 *)
  | Atom (SubsetEq (s1,s2)) ->
      let s1_var = gen_if_not_var (SetT s1) Set in
      let s2_var = gen_if_not_var (SetT s2) Set in
        eq_set (VarSet s2_var) (Union (VarSet s1_var, VarSet s2_var))
  (* not (s1 subset s2) *)
  | NegAtom (SubsetEq (s1,s2)) ->
      let s1_var = gen_if_not_var (SetT s1) Set in
      let s2_var = gen_if_not_var (SetT s2) Set in
      let s = gen_fresh_set_var info in
        let diff_phi = norm_literal info
                          (Atom (InEq (SetT (VarSet s2_var), SetT (s)))) in
        conj_list [eq_set (s) (Union (VarSet s1_var, VarSet s2_var));
                   diff_phi]
  (* p = epsilon *)
  | Atom (Eq (PathT p, PathT Epsilon))
  | Atom (Eq (PathT Epsilon, PathT p))
  | NegAtom (InEq (PathT p, PathT Epsilon))
  | NegAtom (InEq (PathT Epsilon, PathT p)) ->
      let p_var = gen_if_not_var (PathT p) Path in
        Literal (Atom (Append (VarPath p_var, VarPath p_var, VarPath p_var)))
  (* not (p = epsilon) *)
  | NegAtom (Eq (PathT p, PathT Epsilon))
  | NegAtom (Eq (PathT Epsilon, PathT p))
  | Atom (InEq (PathT p, PathT Epsilon))
  | Atom (InEq (PathT Epsilon, PathT p)) ->
      let p_var = gen_if_not_var (PathT p) Path in
        Literal (NegAtom (Append (VarPath p_var, VarPath p_var, VarPath p_var)))

  (* reach(m,a1,a2,i,p) *)
  | Atom (Reach (m,a1,a2,i,p)) ->
      let m_var = gen_if_not_var (MemT m) Mem in
      let a1_var = gen_if_not_var (AddrT a1) Addr in
      let a2_var = gen_if_not_var (AddrT a2) Addr in
      let i_var = gen_if_not_var (IntT i) Int in
      let p_var = gen_if_not_var (PathT p) Path in
      let s = gen_fresh_set_var info in
        let aux_phi = norm_literal info (Atom(In(VarAddr a2_var, s))) in
        conj_list [eq_path (VarPath p_var)
                           (GetPath(VarMem m_var,   VarAddr a1_var,
                                    VarAddr a2_var, VarInt i_var));
                   eq_set (s) (AddrToSet(VarMem m_var, VarAddr a1_var,
                                         VarInt i_var));
                   aux_phi]
  (* not (reach(m,a1,a2,i,p)) *)
  | NegAtom (Reach (m,a1,a2,i,p)) ->
      Not (norm_literal info (Atom (Reach(m,a1,a2,i,p))))

  (* not (ordlist(m,a1,a2)) *)
  | NegAtom (OrderList (m,a1,a2)) ->
    let m_var = gen_if_not_var (MemT m) Mem in
    let a1_var = gen_if_not_var (AddrT a1) Addr in
    let a2_var = gen_if_not_var (AddrT a2) Addr in
    let l1 = gen_fresh_int_var info in
    let l2 = gen_fresh_int_var info in
    let zero = gen_if_not_var (IntT (IntVal 0)) Int in
    let ad1 = gen_fresh_addr_var info in
    let ad2 = gen_fresh_addr_var info in
    let c1 = gen_fresh_cell_var info in
    let c2 = gen_fresh_cell_var info in
    let e1 = gen_fresh_elem_var info in
    let e2 = gen_fresh_elem_var info in
    let aa1 = gen_fresh_addrarr_var info in
    let aa2 = gen_fresh_addrarr_var info in
    let tt1 = gen_fresh_tidarr_var info in
    let tt2 = gen_fresh_tidarr_var info in
    let p = gen_fresh_path_var info in
    let s = gen_fresh_set_var info in
    let phi_ad1_in_s = norm_literal info (Atom(In(ad1,s))) in
    let phi_ad2_in_s = norm_literal info (Atom(In(ad2,s))) in
      conj_list [eq_path p (GetPath(VarMem m_var, VarAddr a1_var, VarAddr a2_var, VarInt zero));
                 eq_set s (PathToSet p);
                 phi_ad1_in_s; phi_ad2_in_s;
                 eq_cell c1 (CellAt(VarMem m_var, VarAddr a1_var));
                 eq_cell c1 (MkCell(e1,aa1,tt1,l1));
                 eq_addr (VarAddr a2_var) (AddrArrRd(aa1,VarInt zero));
                 eq_cell c2 (CellAt(VarMem m_var, VarAddr a2_var));
                 eq_cell c2 (MkCell(e2,aa2,tt2,l2));
                 Literal(Atom(LessElem(e2,e1)));
                 ineq_elem e2 e1]


  (* not (skiplist (m,s,i,a1,a2)) *)
  | NegAtom (Skiplist(m,s,i,a1,a2)) ->
      let m_var = gen_if_not_var (MemT m) Mem in
      let s_var = gen_if_not_var (SetT s) Set in
      let i_var = gen_if_not_var (IntT i) Int in
      let a1_var = gen_if_not_var (AddrT a1) Addr in
      let a2_var = gen_if_not_var (AddrT a2) Addr in
      let p = gen_fresh_path_var info in
      let q = gen_fresh_path_var info in
      let r = gen_fresh_set_var info in
      let u = gen_fresh_set_var info in
      let zero = gen_if_not_var (IntT (IntVal 0)) Int in
      let null = gen_if_not_var (AddrT Null) Addr in
      let a = gen_fresh_addr_var info in
      let c = gen_fresh_cell_var info in
      let e = gen_fresh_elem_var info in
      let aa = gen_fresh_addrarr_var info in
      let tt = gen_fresh_tidarr_var info in
      let l1 = gen_fresh_int_var info in
      let l2 = gen_fresh_int_var info in
      let phi_unordered = norm_literal info (NegAtom(OrderList
                            (VarMem m_var,VarAddr a1_var,VarAddr a2_var))) in
      let phi_diff = norm_literal info (Atom(InEq(SetT (VarSet s_var), SetT r))) in
      let phi_a_in_s = norm_literal info (Atom(In(a,VarSet s_var))) in
      let phi_not_subset = norm_literal info (NegAtom(SubsetEq(r,u))) in
        disj_list
          [(*phi_unordered;*)
           conj_list [eq_path p (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,VarInt zero));
                      eq_set r (PathToSet(p));
                      phi_diff];
           Literal(Atom(Less(VarInt i_var, VarInt  zero)));
           conj_list [phi_a_in_s; eq_cell c (CellAt(VarMem m_var,a));
                      eq_cell c (MkCell(e,aa,tt,l1)); Literal(Atom(Less(VarInt i_var,l1)))];
           conj_list [ineq_int (VarInt i_var) (VarInt zero);
                      Literal(Atom(LessEq(VarInt zero,l2)));
                      Literal(Atom(LessEq(l2,l1)));
                      eq_cell c (CellAt(VarMem m_var,VarAddr a2_var));
                      eq_cell c (MkCell(e,aa,tt,l1));
                      eq_addr a (AddrArrRd(aa,l2));
                      ineq_addr a (VarAddr null)];
           conj_list [ineq_int (VarInt i_var) (VarInt zero);
                      Literal(Atom(LessEq(VarInt zero,l1)));
                      Literal(Atom(Less(l1,VarInt i_var)));
                      eq_int (l2) (IntAdd(l1,IntVal 1));
                      eq_path (p) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l1));
                      eq_path (q) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l2));
                      eq_set (r) (PathToSet p);
                      eq_set (u) (PathToSet q);
                      phi_not_subset]
          ]
(*
        Or(phi_unordered,
        Or(And(eq_path p (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,VarInt zero)),
           And(eq_set r (PathToSet(p)), phi_diff)),
        Or(Literal(Atom(Less(VarInt i_var, VarInt  zero))),
        Or(And(phi_a_in_s,
           And(eq_cell c (CellAt(VarMem m_var,a)),
           And(eq_cell c (MkCell(e,aa,tt,l1)),
               Literal(Atom(Less(VarInt i_var,l1)))))),
        Or(And(ineq_int (VarInt i_var) (VarInt zero),
           And(Literal(Atom(LessEq(VarInt zero,l2))),
           And(Literal(Atom(LessEq(l2,l1))),
           And(eq_cell c (CellAt(VarMem m_var,VarAddr a2_var)),
           And(eq_cell c (MkCell(e,aa,tt,l1)),
           And(eq_addr a (AddrArrRd(aa,l2)),
               ineq_addr a (VarAddr null))))))),
           And(ineq_int (VarInt i_var) (VarInt zero),
           And(Literal(Atom(LessEq(VarInt zero,l1))),
           And(Literal(Atom(Less(l1,VarInt i_var))),
           And(eq_int (l2) (IntAdd(l1,IntVal 1)),
           And(eq_path (p) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l1)),
           And(eq_path (q) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l2)),
           And(eq_set (r) (PathToSet p),
           And(eq_set (u) (PathToSet q),
               phi_not_subset)))))))))))))
*)


  (* All these are normalized, I just need to ensure inside terms are variables *)
  | Atom (Skiplist(m,s,i,a1,a2)) ->
      let m_var = gen_if_not_var (MemT m) Mem in
      let s_var = gen_if_not_var (SetT s) Set in
      let i_var = gen_if_not_var (IntT i) Int in
      let a1_var = gen_if_not_var (AddrT a1) Addr in
      let a2_var = gen_if_not_var (AddrT a2) Addr in
      Literal(Atom(Skiplist(VarMem m_var, VarSet s_var,
                            VarInt i_var, VarAddr a1_var, VarAddr a2_var)))

  (* General inequalities *)
  | Atom (InEq (t1, t2))
  | NegAtom (Eq (t1, t2)) ->
      let t1_var = gen_if_not_var t1 (sort_of_term t1) in
      let t2_var = gen_if_not_var t2 (sort_of_term t2) in
        ineq_term (var_to_term t1_var) (var_to_term t2_var)
  | _ -> Literal l
*)
