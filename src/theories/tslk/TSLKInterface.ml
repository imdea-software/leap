open LeapLib
open LeapVerbose


module Make (SLK : TSLKExpression.S) =
  struct

    module E = Expression

    type varId = E.varId
    type sort  = E.sort
    type tid   = E.tid


    exception UnsupportedSort of string
    exception UnsupportedTSLKExpr of string
    exception UnsupportedExpr of string


    (*****************)
    (* CONFIGURATION *)
    (*****************)

    let fresh_set_name      = E.fresh_set_name
    let fresh_elem_name     = E.fresh_elem_name
    let fresh_tid_name      = E.fresh_tid_name
    let fresh_addr_name     = E.fresh_addr_name
    let fresh_cell_name     = E.fresh_cell_name
    let fresh_setth_name    = E.fresh_setth_name
    let fresh_setelem_name  = E.fresh_setelem_name
    let fresh_path_name     = E.fresh_path_name
    let fresh_mem_name      = E.fresh_mem_name
    let fresh_int_name      = E.fresh_int_name
    let fresh_addrarr_name  = E.fresh_addrarr_name
    let fresh_tidarr_name   = E.fresh_tidarr_name
    let fresh_unknown_name  = E.fresh_unknown_name


    (*******************************)
    (*                             *)
    (*   Normalization functions   *)
    (*                             *)
    (*******************************)


    (* Fresh variables generation *)
    type fresh_var_gen_t =
      {
        tbl : (E.sort, string * int) Hashtbl.t;
        vars : E.VarIdSet.t;
      }


    let new_fresh_gen (vset:E.VarIdSet.t) : fresh_var_gen_t =
      let tbl = Hashtbl.create(20) in
        Hashtbl.add tbl E.Set       (fresh_set_name,     1);
        Hashtbl.add tbl E.Elem      (fresh_elem_name,    1);
        Hashtbl.add tbl E.Tid       (fresh_tid_name,     1);
        Hashtbl.add tbl E.Addr      (fresh_addr_name,    1);
        Hashtbl.add tbl E.Cell      (fresh_cell_name,    1);
        Hashtbl.add tbl E.SetTh     (fresh_setth_name,   1);
        Hashtbl.add tbl E.SetElem   (fresh_setelem_name, 1);
        Hashtbl.add tbl E.Path      (fresh_path_name,    1);
        Hashtbl.add tbl E.Mem       (fresh_mem_name,     1);
        Hashtbl.add tbl E.Int       (fresh_int_name,     1);
        Hashtbl.add tbl E.AddrArray (fresh_addrarr_name, 1);
        Hashtbl.add tbl E.TidArray  (fresh_tidarr_name,  1);
        Hashtbl.add tbl E.Unknown   (fresh_unknown_name, 1);
        {tbl=tbl; vars=vset;}


    let new_fresh_gen_from_formula (phi:E.formula) : fresh_var_gen_t =
      let vars = E.VarSet.fold (fun v s ->
                   E.VarIdSet.add (E.var_id v) s
                 ) (E.all_vars_as_set phi) E.VarIdSet.empty in
      new_fresh_gen vars


    let make_compatible_term_from_var (t:E.term) (v:E.variable) : E.term =
      match t with
      | E.VarT _       -> E.VarT v
      | E.SetT _       -> E.SetT       (E.VarSet v)
      | E.ElemT _      -> E.ElemT      (E.VarElem v)
      | E.TidT _       -> E.TidT       (E.VarTh v)
      | E.AddrT _      -> E.AddrT      (E.VarAddr v)
      | E.CellT _      -> E.CellT      (E.VarCell v)
      | E.SetThT _     -> E.SetThT     (E.VarSetTh v)
      | E.SetIntT _    -> E.SetIntT    (E.VarSetInt v)
      | E.SetElemT _   -> E.SetElemT   (E.VarSetElem v)
      | E.PathT _      -> E.PathT      (E.VarPath v)
      | E.MemT _       -> E.MemT       (E.VarMem v)
      | E.IntT _       -> E.IntT       (E.VarInt v)
      | E.ArrayT _     -> E.ArrayT     (E.VarArray v)
      | E.AddrArrayT _ -> E.AddrArrayT (E.VarAddrArray v)
      | E.TidArrayT _  -> E.TidArrayT  (E.VarTidArray v)


    (* Normalization *)

    type norm_info_t =
      {
        term_map : (E.term, E.variable) Hashtbl.t ;
        processed_term_map : (E.term, E.variable) Hashtbl.t ;
        fresh_gen_info : fresh_var_gen_t ;
      }


    let new_norm_info_from_formula (phi:E.formula) : norm_info_t =
      {
        term_map = Hashtbl.create 10 ;
        processed_term_map = Hashtbl.create 10 ;
        fresh_gen_info = new_fresh_gen_from_formula phi ;
      }


    let gen_fresh_var (gen:fresh_var_gen_t) (s:E.sort) : E.variable =
      let rec find (var_prefix, n) =
        let var_cand_id = Printf.sprintf "%s_%i" var_prefix n in
          if E.VarIdSet.mem var_cand_id gen.vars then
            find (var_prefix, n+1)
          else
            begin
              Hashtbl.replace gen.tbl s (var_prefix, n+1);
              E.build_var var_cand_id s false E.Shared E.GlobalScope E.RealVar
            end
      in
        find (Hashtbl.find gen.tbl s)

    let rec norm_formula (info:norm_info_t) (phi:E.formula) : E.formula =
      let is_var_term t =
        match t with
        | E.VarT(_)
        | E.SetT(E.VarSet _)
        | E.ElemT(E.VarElem _)
        | E.TidT(E.VarTh _)
        | E.AddrT(E.VarAddr _)
        | E.CellT(E.VarCell _)
        | E.SetThT(E.VarSetTh _)
        | E.SetIntT(E.VarSetInt _)
        | E.SetElemT(E.VarSetElem _)
        | E.PathT(E.VarPath _)
        | E.MemT(E.VarMem _)
        | E.IntT(E.VarInt _)
        | E.ArrayT(E.VarArray _)
        | E.AddrArrayT(E.VarAddrArray _)
        | E.TidArrayT(E.VarTidArray _) -> true
        | _ -> false in
      let append_if_diff (t:E.term) (v:E.variable) : unit =
        if is_var_term t then
          (if (E.term_to_var t) <> v then Hashtbl.add info.term_map t v)
        else
          Hashtbl.add info.term_map t v in
      let gen_if_not_var (t:E.term) (s:E.sort) : E.variable =
        if is_var_term t then E.term_to_var t
        else try
               try
                 Hashtbl.find info.processed_term_map t
               with _ -> Hashtbl.find info.term_map t
             with _ -> begin
                         let v = gen_fresh_var info.fresh_gen_info s in
                         append_if_diff t v; v
                       end in

      let rec norm_literal (l:E.literal) : E.literal =
        match l with
        | E.Atom a -> E.Atom (norm_atom a)
        | E.NegAtom a -> E.NegAtom (norm_atom a)

      and norm_set (s:E.set) : E.set =
        match s with
        | E.VarSet v            -> E.VarSet v
        | E.EmptySet            -> E.EmptySet
        | E.Singl a             -> E.Singl (norm_addr a)
        | E.Union (s1,s2)       -> E.Union (norm_set s1, norm_set s2)
        | E.Intr (s1,s2)        -> E.Intr (norm_set s1, norm_set s2)
        | E.Setdiff (s1,s2)     -> E.Setdiff (norm_set s1, norm_set s2)
        | E.PathToSet p         -> E.PathToSet (norm_path p)
        | E.AddrToSet _         -> raise(UnsupportedTSLKExpr(E.set_to_str s))
        | E.AddrToSetAt (m,a,i) -> E.AddrToSetAt (norm_mem m, norm_addr a, norm_int i)
        | E.SetArrayRd _        -> raise(UnsupportedTSLKExpr(E.set_to_str s))

      and norm_tid (t:E.tid) : E.tid =
        match t with
        | E.VarTh v            -> E.VarTh v
        | E.NoTid              -> E.NoTid
        | E.CellLockId _       -> raise(UnsupportedTSLKExpr(E.tid_to_str t))
        | E.CellLockIdAt (c,i) -> E.CellLockIdAt (norm_cell c, norm_int i)
        | E.TidArrayRd _       -> raise(UnsupportedTSLKExpr(E.tid_to_str t))
        | E.TidArrRd _         -> raise(UnsupportedTSLKExpr(E.tid_to_str t))

      and norm_elem (e:E.elem) : E.elem =
        match e with
        | E.VarElem v         -> E.VarElem v
        | E.CellData c        -> E.CellData (norm_cell c)
        | E.ElemArrayRd (E.VarArray v,t) -> E.ElemArrayRd (E.VarArray v, norm_tid t)
        | E.ElemArrayRd _     -> raise(UnsupportedTSLKExpr(E.elem_to_str e))
        | E.HavocListElem     -> raise(UnsupportedTSLKExpr(E.elem_to_str e))
        | E.HavocSkiplistElem -> E.HavocSkiplistElem
        | E.LowestElem        -> E.LowestElem
        | E.HighestElem       -> E.HighestElem

      and norm_addr (a:E.addr) : E.addr =
        match a with
        | E.VarAddr v              -> E.VarAddr v
        | E.Null                   -> E.Null
        | E.Next _                 -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
        | E.NextAt (c,l)           -> E.NextAt (norm_cell c, norm_int l)
        | E.ArrAt (c,l)            -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
        | E.FirstLocked (m,p)      -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
        | E.FirstLockedAt (m,p,l)  -> E.FirstLockedAt (norm_mem m, norm_path p, norm_int l)
        | E.AddrArrayRd (E.VarArray v,t) -> E.AddrArrayRd (E.VarArray v, norm_tid t)
        | E.AddrArrayRd _          -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
        | E.AddrArrRd (aa,i)       -> let a_var = gen_if_not_var (E.AddrT a) E.Addr in
                                        E.VarAddr a_var

      and norm_cell (c:E.cell) : E.cell =
        match c with
        | E.VarCell v            -> E.VarCell v
        | E.Error                -> E.Error
        | E.MkCell _             -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
        | E.MkSLKCell (e,aa,tt)  -> E.MkSLKCell(norm_elem e, List.map norm_addr aa, List.map norm_tid tt)
        | E.MkSLCell (e,aa,tt,l) -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
        | E.CellLock _           -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
        | E.CellLockAt (c,i,t)   -> E.CellLockAt (norm_cell c, norm_int i, norm_tid t)
        | E.CellUnlock _         -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
        | E.CellUnlockAt (c,i)   -> E.CellUnlockAt (norm_cell c, norm_int i)
        | E.CellAt (m,a)         -> E.CellAt (norm_mem m, norm_addr a)
        | E.CellArrayRd (E.VarArray v,t) -> E.CellArrayRd (E.VarArray v, norm_tid t)
        | E.CellArrayRd _        -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
        | E.UpdCellAddr (c,i,a)  -> E.UpdCellAddr (norm_cell c, norm_int i, norm_addr a)

      and norm_setth (s:E.setth) : E.setth =
        match s with
        | E.VarSetTh v        -> E.VarSetTh v
        | E.EmptySetTh        -> E.EmptySetTh
        | E.SinglTh t         -> E.SinglTh (norm_tid t)
        | E.UnionTh (s1,s2)   -> E.UnionTh (norm_setth s1, norm_setth s2)
        | E.IntrTh (s1,s2)    -> E.IntrTh (norm_setth s1, norm_setth s2)
        | E.SetdiffTh (s1,s2) -> E.SetdiffTh (norm_setth s1, norm_setth s2)
        | E.SetThArrayRd (E.VarArray v,t) -> E.SetThArrayRd (E.VarArray v, norm_tid t)
        | E.SetThArrayRd _    -> raise(UnsupportedTSLKExpr(E.setth_to_str s))

      and norm_setint (s:E.setint) : E.setint =
        match s with
        | E.VarSetInt v         -> E.VarSetInt v
        | E.EmptySetInt         -> E.EmptySetInt
        | E.SinglInt i          -> E.SinglInt (norm_int i)
        | E.UnionInt (s1,s2)    -> E.UnionInt (norm_setint s1, norm_setint s2)
        | E.IntrInt (s1,s2)     -> E.IntrInt (norm_setint s1, norm_setint s2)
        | E.SetdiffInt (s1,s2)  -> E.SetdiffInt (norm_setint s1, norm_setint s2)
        | E.SetIntArrayRd (E.VarArray v,t) -> E.SetIntArrayRd (E.VarArray v, norm_tid t)
        | E.SetIntArrayRd _     -> raise(UnsupportedTSLKExpr(E.setint_to_str s))

      and norm_setelem (s:E.setelem) : E.setelem =
        match s with
        | E.VarSetElem v        -> E.VarSetElem v
        | E.EmptySetElem        -> E.EmptySetElem
        | E.SinglElem e         -> E.SinglElem (norm_elem e)
        | E.UnionElem (s1,s2)   -> E.UnionElem (norm_setelem s1, norm_setelem s2)
        | E.IntrElem (s1,s2)    -> E.IntrElem (norm_setelem s1, norm_setelem s2)
        | E.SetdiffElem (s1,s2) -> E.SetdiffElem (norm_setelem s1, norm_setelem s2)
        | E.SetToElems (s,m)    -> E.SetToElems (norm_set s, norm_mem m)
        | E.SetElemArrayRd (E.VarArray v,t) -> E.SetElemArrayRd(E.VarArray v, norm_tid t)
        | E.SetElemArrayRd _      -> raise(UnsupportedTSLKExpr(E.setelem_to_str s))

      and norm_path (p:E.path) : E.path =
        match p with
        | E.VarPath v             -> E.VarPath v
        | E.Epsilon               -> E.Epsilon
        | E.SimplePath a          -> E.SimplePath (norm_addr a)
        | E.GetPath _             -> raise(UnsupportedTSLKExpr(E.path_to_str p))
        | E.GetPathAt (m,a1,a2,i) -> E.GetPathAt (norm_mem m, norm_addr a1, norm_addr a2, norm_int i)
        | E.PathArrayRd (E.VarArray v,t) -> E.PathArrayRd (E.VarArray v, norm_tid t)
        | E.PathArrayRd _         -> raise(UnsupportedTSLKExpr(E.path_to_str p))

      and norm_mem (m:E.mem) : E.mem =
        match m with
        | E.VarMem v       -> E.VarMem v
        | E.Update (m,a,c) -> E.Update (norm_mem m, norm_addr a, norm_cell c)
        | E.MemArrayRd (E.VarArray v,t) -> E.MemArrayRd (E.VarArray v, norm_tid t)
        | E.MemArrayRd _   -> raise(UnsupportedTSLKExpr(E.mem_to_str m))

      and norm_int (i:E.integer) : E.integer =
        match i with
        | E.IntVal j       -> E.IntVal j
        | E.VarInt v       -> E.VarInt v
        | E.IntNeg j       -> E.IntNeg j
        | E.IntAdd (j1,j2) -> E.IntAdd (j1,j2)
        | E.IntSub (j1,j2) -> E.IntSub (j1,j2)
        | E.IntMul (j1,j2) -> E.IntMul (j1,j2)
        | E.IntDiv (j1,j2) -> E.IntDiv (j1,j2)
        | E.CellMax (c)    -> E.CellMax (norm_cell c)
        | E.IntArrayRd _   -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
        | E.IntSetMin _    -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
        | E.IntSetMax _    -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
        | E.HavocLevel     -> E.HavocLevel

      and norm_arrays (arr:E.arrays) : E.arrays =
        match arr with
        | E.VarArray v      -> E.VarArray v
        | E.ArrayUp (a,t,e) -> E.ArrayUp (norm_arrays a, norm_tid t, norm_expr e)

      and norm_addrarr (aa:E.addrarr) : E.addrarr =
        match aa with
        | E.VarAddrArray v       -> E.VarAddrArray v
        | E.AddrArrayUp (bb,i,a) -> E.AddrArrayUp (norm_addrarr bb, norm_int i, norm_addr a)
        | E.CellArr c            -> raise(UnsupportedTSLKExpr(E.addrarr_to_str aa))

      and norm_tidarr (tt:E.tidarr) : E.tidarr =
        match tt with
        | E.VarTidArray v       -> E.VarTidArray v
        | E.TidArrayUp (yy,i,t) -> E.TidArrayUp (norm_tidarr yy, norm_int i, norm_tid t)
        | E.CellTids c          -> raise(UnsupportedTSLKExpr(E.tidarr_to_str tt))

      and norm_term (t:E.term) : E.term =
        match t with
        | E.VarT v             -> E.VarT v
        | E.SetT s             -> E.SetT (norm_set s)
        | E.ElemT e            -> E.ElemT (norm_elem e)
        | E.TidT t             -> E.TidT (norm_tid t)
        | E.AddrT a            -> E.AddrT (norm_addr a)
        | E.CellT c            -> E.CellT (norm_cell c)
        | E.SetThT s           -> E.SetThT (norm_setth s)
        | E.SetIntT s          -> E.SetIntT (norm_setint s)
        | E.SetElemT s         -> E.SetElemT (norm_setelem s)
        | E.PathT p            -> E.PathT (norm_path p)
        | E.MemT m             -> E.MemT (norm_mem m)
        | E.IntT i             -> E.IntT (norm_int i)
        | E.ArrayT arr         -> E.ArrayT (norm_arrays arr)
        | E.AddrArrayT aa      -> E.AddrArrayT (norm_addrarr aa)
        | E.TidArrayT tt       -> E.TidArrayT (norm_tidarr tt)

      and norm_expr (expr:E.expr_t) : E.expr_t =
        match expr with
        | E.Term t -> E.Term (norm_term t)
        | E.Formula f -> E.Formula (norm_formula info f)

      and norm_atom (a:E.atom) : E.atom =
        match a with
        | E.Append (p1,p2,p3)     -> E.Append (norm_path p1, norm_path p2, norm_path p3)
        | E.Reach _               -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.ReachAt (m,a1,a2,i,p) -> E.ReachAt (norm_mem m, norm_addr a1, norm_addr a2,
                                          norm_int i, norm_path p)
        | E.OrderList (m,a1,a2)   -> E.OrderList (norm_mem m, norm_addr a1, norm_addr a2)
        | E.Skiplist _            -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.In (a,s)              -> E.In (norm_addr a, norm_set s)
        | E.SubsetEq (s1,s2)      -> E.SubsetEq (norm_set s1, norm_set s2)
        | E.InTh (t,s)            -> E.InTh (norm_tid t, norm_setth s)
        | E.SubsetEqTh (s1,s2)    -> E.SubsetEqTh (norm_setth s1, norm_setth s2)
        | E.InInt _               -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.SubsetEqInt _         -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.InElem (e,s)          -> E.InElem (norm_elem e, norm_setelem s)
        | E.SubsetEqElem (s1,s2)  -> E.SubsetEqElem (norm_setelem s1, norm_setelem s2)
        | E.Less (i1,i2)          -> E.Less (norm_int i1, norm_int i2)
        | E.Greater (i1,i2)       -> E.Greater (norm_int i1, norm_int i2)
        | E.LessEq (i1,i2)        -> E.LessEq (norm_int i1, norm_int i2)
        | E.GreaterEq (i1,i2)     -> E.GreaterEq (norm_int i1, norm_int i2)
        | E.LessTid _             -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.LessElem (e1,e2)      -> E.LessElem (norm_elem e1, norm_elem e2)
        | E.GreaterElem (e1,e2)   -> E.GreaterElem (norm_elem e1, norm_elem e2)
        | E.Eq (t1,t2)            -> E.Eq (norm_term t1, norm_term t2)
        | E.InEq (t1,t2)          -> E.InEq (norm_term t1, norm_term t2)
        | E.BoolVar v             -> E.BoolVar v
        | E.BoolArrayRd _         -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
        | E.PC (i,topt,pr)        -> let norm_topt =
                                       match topt with
                                       | E.Shared -> E.Shared
                                       | E.Local t -> E.Local (norm_tid t) in
                                     E.PC (i, norm_topt, pr)
        | E.PCUpdate (i,t)        -> E.PCUpdate (i, norm_tid t)
        | E.PCRange (i,j,topt,pr) -> let norm_topt =
                                       match topt with
                                       | E.Shared -> E.Shared
                                       | E.Local t -> E.Local (norm_tid t) in
                                     E.PCRange (i, j, norm_topt, pr)
    in
      match phi with
      | E.Literal l                     -> E.Literal (norm_literal l)
      | E.True                          -> E.True
      | E.False                         -> E.False
      | E.And (psi1,psi2)               -> E.And (norm_formula info psi1,
                                                  norm_formula info psi2)
      | E.Or (psi1,psi2)                -> E.Or (norm_formula info psi1,
                                                 norm_formula info psi2)
      | E.Not (E.Literal (E.Atom a))    -> E.Literal (norm_literal (E.NegAtom a))
      | E.Not (E.Literal (E.NegAtom a)) -> norm_formula info (E.Literal (E.Atom a))
      | E.Not psi                       -> E.Not (norm_formula info psi)
      | E.Implies (psi1,psi2)           -> E.Implies (norm_formula info psi1,
                                                      norm_formula info psi2)
      | E.Iff (psi1,psi2)               -> E.Iff (norm_formula info psi1,
                                                  norm_formula info psi2)




    let norm_to_tslk (phi:E.formula) : E.formula =
      (* REVIEW THIS WHOLE FORMULA *)
      (* Create a new normalization *)
      let norm_info = new_norm_info_from_formula phi in
      (* Process the original formula *)
      let phi' = norm_formula norm_info phi in
      (* Normalize all remaining literals stored in the normalization table *)
      let lit_list = ref [] in
      while (Hashtbl.length norm_info.term_map > 0) do
        Hashtbl.iter (fun t v ->
          begin
            Hashtbl.add norm_info.processed_term_map t v;
            let l = E.Literal (E.Atom (E.Eq (make_compatible_term_from_var t v, t))) in
            let new_l = norm_formula norm_info l in
            let lit_to_add = match new_l with
                             | E.Literal(E.Atom(E.Eq(t1,t2)))
                             | E.Literal(E.NegAtom(E.InEq(t1,t2))) ->
                                  if t1 <> t2 then new_l else l
                             | _ -> new_l in
            lit_list := lit_to_add :: !lit_list
          end;
          Hashtbl.remove norm_info.term_map t
        ) norm_info.term_map;
      done;
      if !lit_list = [] then
        phi'
      else
        match phi' with
        | E.Implies (ante, conseq) -> E.Implies(E.And(E.conj_list !lit_list, ante),conseq)
        | _ -> E.And (E.conj_list !lit_list, phi')






    (* Machinery for array conversion *)
    let addrarr_tbl : (E.addrarr, SLK.addr list) Hashtbl.t = Hashtbl.create 10


    let rec expand_array_to_var (v:E.variable)
                            (s:SLK.sort)
                            (n:int) : SLK.variable =
      let id_str = E.var_id v in
      let pr_str = if E.var_is_primed v then "_prime" else "" in
      let th_str = match E.var_parameter v with
                   | E.Shared -> ""
                   | E.Local tid -> "_" ^ (E.tid_to_str tid) in
      let p_str = match E.var_scope v with
                  | E.GlobalScope -> ""
                  | E.Scope p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = SLK.build_var new_id s false SLK.Shared SLK.GlobalScope in
      verb "FRESH VAR: %s\n" new_id;
      SLK.variable_mark_fresh v_fresh true;
      v_fresh


    and gen_addr_list (aa:E.addrarr) : SLK.addr list =
      let xs = ref [] in
      for n = (SLK.k - 1) downto 0 do
        let v = match aa with
                | E.VarAddrArray v ->
                    SLK.VarAddr (expand_array_to_var v SLK.Addr n)
                | E.CellArr c -> raise(UnsupportedTSLKExpr(E.addrarr_to_str aa))
                | _ -> SLK.Null in
        xs := v::(!xs)
      done;
      verb "**** TSL Solver, generated address list for %s: [%s]\n"
              (E.addrarr_to_str aa)
              (String.concat ";" (List.map SLK.addr_to_str !xs));
      !xs


    and get_addr_list (aa:E.addrarr) : SLK.addr list =
      try
        Hashtbl.find addrarr_tbl aa
      with _ -> begin
        let aa' = gen_addr_list aa in
        Hashtbl.add addrarr_tbl aa aa'; aa'
      end


    (* Expression to TSLKExpression conversion *)
    and sort_to_tslk_sort (s:E.sort) : SLK.sort =
      match s with
        E.Set       -> SLK.Set
      | E.Elem      -> SLK.Elem
      | E.Tid      -> SLK.Tid
      | E.Addr      -> SLK.Addr
      | E.Cell      -> SLK.Cell
      | E.SetTh     -> SLK.SetTh
      | E.SetInt    -> raise(UnsupportedSort(E.sort_to_str s))
      | E.SetElem   -> SLK.SetElem
      | E.Path      -> SLK.Path
      | E.Mem       -> SLK.Mem
      | E.Bool      -> SLK.Bool
      | E.Int       -> SLK.Level
      | E.Array     -> raise(UnsupportedSort(E.sort_to_str s))
      | E.AddrArray -> raise(UnsupportedSort(E.sort_to_str s))
      | E.TidArray  -> raise(UnsupportedSort(E.sort_to_str s))
      | E.Unknown   -> SLK.Unknown


    and build_term_var (v:E.variable) : SLK.term =
      let tslk_v = var_to_tslk_var v in
      match (E.var_sort v) with
        E.Set       -> SLK.SetT       (SLK.VarSet        tslk_v)
      | E.Elem      -> SLK.ElemT      (SLK.VarElem       tslk_v)
      | E.Tid      -> SLK.TidT      (SLK.VarTh         tslk_v)
      | E.Addr      -> SLK.AddrT      (SLK.VarAddr       tslk_v)
      | E.Cell      -> SLK.CellT      (SLK.VarCell       tslk_v)
      | E.SetTh     -> SLK.SetThT     (SLK.VarSetTh      tslk_v)
      | E.Path      -> SLK.PathT      (SLK.VarPath       tslk_v)
      | E.Mem       -> SLK.MemT       (SLK.VarMem        tslk_v)
      | E.Int       -> SLK.LevelT     (SLK.VarLevel      tslk_v)
      | _              -> SLK.VarT       (tslk_v)



    and var_to_tslk_var (v:E.variable) : SLK.variable =
      SLK.build_var (E.var_id v)
                    (sort_to_tslk_sort (E.var_sort v))
                    (E.var_is_primed v)
                    (shared_to_tslk_shared (E.var_parameter v))
                    (scope_to_tslk_scope (E.var_scope v))


    and shared_to_tslk_shared (th:E.shared_or_local) : SLK.shared_or_local =
      match th with
      | E.Shared -> SLK.Shared
      | E.Local t -> SLK.Local (tid_to_tslk_tid t)


    and scope_to_tslk_scope (p:E.procedure_name) : SLK.procedure_name =
      match p with
      | E.GlobalScope -> SLK.GlobalScope
      | E.Scope proc -> SLK.Scope proc


    and tid_to_tslk_tid (th:E.tid) : SLK.tid =
      match th with
        E.VarTh v            -> SLK.VarTh (var_to_tslk_var v)
      | E.NoTid              -> SLK.NoTid
      | E.CellLockId _       -> raise(UnsupportedTSLKExpr(E.tid_to_str th))
      | E.CellLockIdAt (c,l) -> SLK.CellLockIdAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l)
      | E.TidArrayRd _       -> raise(UnsupportedTSLKExpr(E.tid_to_str th))
      | E.TidArrRd (tt,i)    -> raise(UnsupportedTSLKExpr(E.tid_to_str th))

    and term_to_tslk_term (t:E.term) : SLK.term =
      match t with
        E.VarT v        -> SLK.VarT (var_to_tslk_var v)
      | E.SetT s        -> SLK.SetT (set_to_tslk_set s)
      | E.ElemT e       -> SLK.ElemT (elem_to_tslk_elem e)
      | E.TidT t        -> SLK.TidT (tid_to_tslk_tid t)
      | E.AddrT a       -> SLK.AddrT (addr_to_tslk_addr a)
      | E.CellT c       -> SLK.CellT (cell_to_tslk_cell c)
      | E.SetThT st     -> SLK.SetThT (setth_to_tslk_setth st)
      | E.SetIntT _     -> raise(UnsupportedTSLKExpr(E.term_to_str t))
      | E.SetElemT st   -> SLK.SetElemT (setelem_to_tslk_setelem st)
      | E.PathT p       -> SLK.PathT (path_to_tslk_path p)
      | E.MemT m        -> SLK.MemT (mem_to_tslk_mem m)
      | E.IntT i        -> SLK.LevelT (int_to_tslk_level i)
      | E.AddrArrayT aa -> raise(UnsupportedTSLKExpr(E.term_to_str t))
      | E.TidArrayT tt  -> raise(UnsupportedTSLKExpr(E.term_to_str t))
      | E.ArrayT a      -> arrays_to_tslk_term a


    and arrays_to_tslk_term (a:E.arrays) : SLK.term =
      match a with
      | E.VarArray v -> build_term_var v
      | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
          let tslk_v  = var_to_tslk_var v in
          let tslk_th = tid_to_tslk_tid th_p in
          let tslk_t  = term_to_tslk_term t
          in
            SLK.VarUpdate (tslk_v, tslk_th, tslk_t)
      | E.ArrayUp (_,_,e) -> raise(UnsupportedTSLKExpr(E.expr_to_str e))


    and set_to_tslk_set (s:E.set) : SLK.set =
      let to_set = set_to_tslk_set in
      match s with
        E.VarSet v            -> SLK.VarSet (var_to_tslk_var v)
      | E.EmptySet            -> SLK.EmptySet
      | E.Singl a             -> SLK.Singl (addr_to_tslk_addr a)
      | E.Union (s1,s2)       -> SLK.Union (to_set s1, to_set s2)
      | E.Intr (s1,s2)        -> SLK.Intr (to_set s1, to_set s2)
      | E.Setdiff (s1,s2)     -> SLK.Setdiff (to_set s1, to_set s2)
      | E.PathToSet p         -> SLK.PathToSet (path_to_tslk_path p)
      | E.AddrToSet _         -> raise(UnsupportedTSLKExpr(E.set_to_str s))
      | E.AddrToSetAt (m,a,l) -> SLK.AddrToSet (mem_to_tslk_mem m,
                                                    addr_to_tslk_addr a,
                                                    int_to_tslk_level l)
      | E.SetArrayRd (E.VarArray v,t) ->
          SLK.VarSet (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.SetArrayRd _        -> raise(UnsupportedTSLKExpr(E.set_to_str s))


    and elem_to_tslk_elem (e:E.elem) : SLK.elem =
      match e with
        E.VarElem v              -> SLK.VarElem (var_to_tslk_var v)
      | E.CellData c             -> SLK.CellData (cell_to_tslk_cell c)
      | E.ElemArrayRd (E.VarArray v,t) ->
          SLK.VarElem (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.ElemArrayRd _          -> raise(UnsupportedTSLKExpr(E.elem_to_str e))
      | E.HavocListElem          -> raise(UnsupportedTSLKExpr(E.elem_to_str e))
      | E.HavocSkiplistElem      -> SLK.HavocSkiplistElem
      | E.LowestElem             -> SLK.LowestElem
      | E.HighestElem            -> SLK.HighestElem


    and addr_to_tslk_addr (a:E.addr) : SLK.addr =
      match a with
        E.VarAddr v              -> SLK.VarAddr (var_to_tslk_var v)
      | E.Null                   -> SLK.Null
      | E.Next _                 -> raise(UnsupportedTSLKExpr(E.addr_to_str a))

      | E.NextAt (c,l)           -> SLK.NextAt (cell_to_tslk_cell c, int_to_tslk_level l)
      | E.ArrAt (c,l)            -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
      | E.FirstLocked (m,p)      -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
      | E.FirstLockedAt (m,p,l)  -> SLK.FirstLockedAt (mem_to_tslk_mem m,
                                                          path_to_tslk_path p,
                                                          int_to_tslk_level l)
      | E.AddrArrayRd (E.VarArray v,t) ->
          SLK.VarAddr (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.AddrArrayRd _          -> raise(UnsupportedTSLKExpr(E.addr_to_str a))
      | E.AddrArrRd (aa,i)       -> raise(UnsupportedTSLKExpr(E.addr_to_str a))


    and cell_to_tslk_cell (c:E.cell) : SLK.cell =
      match c with
        E.VarCell v            -> SLK.VarCell (var_to_tslk_var v)
      | E.Error                -> SLK.Error
      | E.MkCell _             -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
      | E.MkSLKCell (e,aa,tt)  ->
          if List.length aa > SLK.k || List.length tt > SLK.k then
            begin
              Interface.Err.msg "Too many addresses or threads ids in MkCell" $
                Printf.sprintf "Tried to build a term:\n%s\n while in TSLK[%i]. \
                                Notice the number of addresses or threads identifiers \
                                exceeds the parameter of the theory."
                                (E.cell_to_str c) SLK.k;
              raise(UnsupportedTSLKExpr(E.cell_to_str c))
            end
          else
            let aa_pad = LeapLib.list_of (SLK.k - List.length aa) SLK.Null in
            let tt_pad = LeapLib.list_of (SLK.k - List.length tt) SLK.NoTid in
            SLK.MkCell (elem_to_tslk_elem e,
                         (List.map addr_to_tslk_addr aa) @ aa_pad,
                         (List.map tid_to_tslk_tid tt) @ tt_pad)
      | E.MkSLCell (e,aa,tt,l) -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
      (* TSLK receives two arguments, while current epxression receives only one *)
      (* However, for the list examples, I think we will not need it *)
      | E.CellLock _           -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
      | E.CellLockAt (c,l,t)   -> SLK.CellLockAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l,
                                                     tid_to_tslk_tid t)
      | E.CellUnlock _         -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
      | E.CellUnlockAt (c,l)   -> SLK.CellUnlockAt (cell_to_tslk_cell c,
                                                       int_to_tslk_level l)
      | E.CellAt (m,a)         -> SLK.CellAt (mem_to_tslk_mem m, addr_to_tslk_addr a)
      | E.CellArrayRd (E.VarArray v,t) ->
          SLK.VarCell (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.CellArrayRd _        -> raise(UnsupportedTSLKExpr(E.cell_to_str c))
      | E.UpdCellAddr (c,i,a)  -> raise(UnsupportedTSLKExpr(E.cell_to_str c))


    and setth_to_tslk_setth (st:E.setth) : SLK.setth =
      let to_setth = setth_to_tslk_setth in
      match st with
        E.VarSetTh v        -> SLK.VarSetTh (var_to_tslk_var v)
      | E.EmptySetTh        -> SLK.EmptySetTh
      | E.SinglTh t         -> SLK.SinglTh (tid_to_tslk_tid t)
      | E.UnionTh (s1,s2)   -> SLK.UnionTh (to_setth s1, to_setth s2)
      | E.IntrTh (s1,s2)    -> SLK.IntrTh (to_setth s1, to_setth s2)
      | E.SetdiffTh (s1,s2) -> SLK.SetdiffTh (to_setth s1, to_setth s2)
      | E.SetThArrayRd (E.VarArray v,t) ->
          SLK.VarSetTh (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.SetThArrayRd _    -> raise(UnsupportedTSLKExpr(E.setth_to_str st))


    and setelem_to_tslk_setelem (st:E.setelem) : SLK.setelem =
      let to_setelem = setelem_to_tslk_setelem in
      match st with
        E.VarSetElem v        -> SLK.VarSetElem (var_to_tslk_var v)
      | E.EmptySetElem        -> SLK.EmptySetElem
      | E.SinglElem e         -> SLK.SinglElem (elem_to_tslk_elem e)
      | E.UnionElem (s1,s2)   -> SLK.UnionElem (to_setelem s1, to_setelem s2)
      | E.IntrElem (s1,s2)    -> SLK.IntrElem (to_setelem s1, to_setelem s2)
      | E.SetdiffElem (s1,s2) -> SLK.SetdiffElem (to_setelem s1, to_setelem s2)
      | E.SetElemArrayRd (E.VarArray v,t) ->
          SLK.VarSetElem (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.SetToElems (s,m)    -> SLK.SetToElems (set_to_tslk_set s,
                                                    mem_to_tslk_mem m)
      | E.SetElemArrayRd _    -> raise(UnsupportedTSLKExpr(E.setelem_to_str st))


    and path_to_tslk_path (p:E.path) : SLK.path =
      match p with
        E.VarPath v             -> SLK.VarPath (var_to_tslk_var v)
      | E.Epsilon               -> SLK.Epsilon
      | E.SimplePath a          -> SLK.SimplePath (addr_to_tslk_addr a)
      | E.GetPath _             -> raise(UnsupportedTSLKExpr(E.path_to_str p))
      | E.GetPathAt (m,a1,a2,l) -> SLK.GetPathAt (mem_to_tslk_mem m,
                                                      addr_to_tslk_addr a1,
                                                      addr_to_tslk_addr a2,
                                                      int_to_tslk_level l)
      | E.PathArrayRd (E.VarArray v,t) ->
          SLK.VarPath (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.PathArrayRd _         -> raise(UnsupportedTSLKExpr(E.path_to_str p))


    and mem_to_tslk_mem (m:E.mem) : SLK.mem =
      match m with
        E.VarMem v       -> SLK.VarMem (var_to_tslk_var v)
      | E.Update (m,a,c) -> SLK.Update (mem_to_tslk_mem m,
                                           addr_to_tslk_addr a,
                                           cell_to_tslk_cell c)
      (* Missing the case for "emp" *)
      | E.MemArrayRd (E.VarArray v,t) ->
          SLK.VarMem (var_to_tslk_var (E.var_set_param (E.Local t) v))
      | E.MemArrayRd _        -> raise(UnsupportedTSLKExpr(E.mem_to_str m))


    and int_to_tslk_level (i:E.integer) : SLK.level =
      let rec apply n f x = if n <= 1 then f x else apply (n-1) f (f x) in
      let succ = (fun x -> SLK.LevelSucc x) in
      let pred = (fun x -> SLK.LevelPred x) in
      let tolevel = int_to_tslk_level in
      match i with
        E.IntVal l       -> (*if l < 0 || SLK.k <= l then
                                 begin
                                   Interface.Err.msg "Level out of bounds" $
                                   Printf.sprintf "Level %i is out of the bounds of TSLK[%i], \
                                                   which goes from 0 to %i."
                                      l SLK.k (SLK.k-1);
                                   raise(UnsupportedTSLKExpr(E.integer_to_str i))
                                 end
                               else *)
                                 SLK.LevelVal l
      | E.VarInt v       -> SLK.VarLevel (var_to_tslk_var v)
      | E.IntNeg i       -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.IntAdd (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (E.IntVal j1, E.IntVal j2) -> SLK.LevelVal (j1+j2)
                                 | (E.VarInt v , E.IntVal j ) -> apply j succ (tolevel i1)
                                 | (E.IntVal j , E.VarInt v ) -> apply j succ (tolevel i2)
                                 | _ -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
                               end
      | E.IntSub (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (E.IntVal j1, E.IntVal j2) -> SLK.LevelVal (j1-j2)
                                 | (E.VarInt v , E.IntVal j ) -> apply j pred (tolevel i1)
                                 | _ -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
                               end
      | E.IntMul (i1,i2) -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.IntDiv (i1,i2) -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.CellMax (c)    -> SLK.LevelVal SLK.k
      | E.IntArrayRd _   -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.IntSetMin _    -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.IntSetMax _    -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
      | E.HavocLevel     -> SLK.HavocLevel


    and atom_to_tslk_atom (a:E.atom) : SLK.atom =
      let path    = path_to_tslk_path       in
      let mem     = mem_to_tslk_mem         in
      let addr    = addr_to_tslk_addr       in
      let elem    = elem_to_tslk_elem       in
      let set     = set_to_tslk_set         in
      let tid     = tid_to_tslk_tid         in
      let setth   = setth_to_tslk_setth     in
      let setelem = setelem_to_tslk_setelem in
      let integ   = int_to_tslk_level       in
      let term    = term_to_tslk_term       in
      match a with
        E.Append (p1,p2,p3)    -> SLK.Append (path p1,path p2,path p3)
      | E.Reach _              -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.ReachAt (m,a1,a2,l,p)-> SLK.Reach (mem m, addr a1, addr a2, integ l, path p)
      | E.OrderList(m,a1,a2)   -> SLK.OrderList (mem m, addr a1, addr a2)
      | E.Skiplist _           -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.In (a,s)             -> SLK.In (addr a, set s)
      | E.SubsetEq (s1,s2)     -> SLK.SubsetEq (set s1, set s2)
      | E.InTh (t,s)           -> SLK.InTh (tid t, setth s)
      | E.SubsetEqTh (s1,s2)   -> SLK.SubsetEqTh (setth s1, setth s2)
      | E.InInt _              -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.SubsetEqInt _        -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.InElem (e,s)         -> SLK.InElem (elem_to_tslk_elem e, setelem s)
      | E.SubsetEqElem (s1,s2) -> SLK.SubsetEqElem (setelem s1, setelem s2)
      | E.Less (i1,i2)         -> SLK.Less (integ i1, integ i2)
      | E.Greater (i1,i2)      -> SLK.Greater (integ i1, integ i2)
      | E.LessEq (i1,i2)       -> SLK.LessEq (integ i1, integ i2)
      | E.GreaterEq (i1,i2)    -> SLK.GreaterEq (integ i1, integ i2)
      | E.LessTid _            -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.LessElem (e1,e2)     -> SLK.LessElem (elem e1, elem e2)
      | E.GreaterElem (e1,e2)  -> SLK.GreaterElem (elem e1, elem e2)
      | E.Eq (t1,t2)           -> SLK.Eq (term t1, term t2)
      | E.InEq (t1,t2)         -> SLK.InEq (term t1, term t2)
      | E.BoolVar v            -> SLK.BoolVar (var_to_tslk_var v)
      | E.BoolArrayRd _        -> raise(UnsupportedTSLKExpr(E.atom_to_str a))
      | E.PC (pc,t,pr)         -> SLK.PC (pc, shared_to_tslk_shared t,pr)
      | E.PCUpdate (pc,t)      -> SLK.PCUpdate (pc, tid_to_tslk_tid t)
      | E.PCRange (pc1,pc2,t,pr) -> SLK.PCRange (pc1, pc2, shared_to_tslk_shared t, pr)


    and literal_to_tslk_literal (l:E.literal) : SLK.literal =
      match l with
        E.Atom a    -> SLK.Atom (atom_to_tslk_atom a)
      | E.NegAtom a -> SLK.NegAtom (atom_to_tslk_atom a)


    and formula_to_tslk_formula_aux (f:E.formula) : SLK.formula =
(*      LOG "Entering formula_to_tslk_formula_aux..." LEVEL TRACE; *)
      let to_formula = formula_to_tslk_formula_aux in
      match f with
      (* Translation of literals of the form B = A {l <- a} *)
      | E.Literal(E.Atom(E.Eq(E.AddrArrayT(E.VarAddrArray _ as bb),E.AddrArrayT(E.AddrArrayUp(aa,l,a)))))
      | E.Literal(E.Atom(E.Eq(E.AddrArrayT(E.AddrArrayUp(aa,l,a)),E.AddrArrayT(E.VarAddrArray _ as bb))))
      | E.Literal(E.NegAtom(E.InEq(E.AddrArrayT(E.VarAddrArray _ as bb),E.AddrArrayT(E.AddrArrayUp(aa,l,a)))))
      | E.Literal(E.NegAtom(E.InEq(E.AddrArrayT(E.AddrArrayUp(aa,l,a)),E.AddrArrayT(E.VarAddrArray _ as bb)))) ->
          begin
            let a' = addr_to_tslk_addr a in
            let l' = int_to_tslk_level l in
            let aa' = get_addr_list aa in
            let bb' = get_addr_list bb in
            let xs = ref [] in
            for n = 0 to (SLK.k - 1) do
              let n' = SLK.LevelVal n in
              xs := (SLK.Implies
                      (SLK.eq_level l' n',
                       SLK.eq_addr a' (List.nth bb' n))) ::
                    (SLK.Implies
                      (SLK.ineq_level l' n',
                       SLK.eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                    (!xs)
            done;
            SLK.addr_mark_smp_interesting a' true;
            SLK.conj_list (!xs)
          end
      (* Translation of literals of the form a = A[i] *)
      | E.Literal(E.Atom(E.Eq(E.AddrT a,E.AddrT(E.AddrArrRd(aa,i)))))
      | E.Literal(E.Atom(E.Eq(E.AddrT(E.AddrArrRd(aa,i)),E.AddrT a)))
      | E.Literal(E.NegAtom(E.InEq(E.AddrT a,E.AddrT(E.AddrArrRd(aa,i)))))
      | E.Literal(E.NegAtom(E.InEq(E.AddrT(E.AddrArrRd(aa,i)),E.AddrT a))) ->
          let a' = addr_to_tslk_addr a in
          let aa' = get_addr_list aa in
          let i' = int_to_tslk_level i in
          let xs = ref [] in
          for n = 0 to (SLK.k - 1) do
            let n' = SLK.LevelVal n in
            xs := (SLK.Implies
                    (SLK.eq_level i' n',
                     SLK.eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          SLK.addr_mark_smp_interesting a' true;
          SLK.conj_list (!xs)
      (* Translation of literals of the form a = c.nextat[i] *)
      | E.Literal(E.Atom(E.Eq(E.AddrT a,E.AddrT(E.NextAt(c,i)))))
      | E.Literal(E.Atom(E.Eq(E.AddrT(E.NextAt(c,i)),E.AddrT a)))
      | E.Literal(E.NegAtom(E.InEq(E.AddrT a,E.AddrT(E.NextAt(c,i)))))
      | E.Literal(E.NegAtom(E.InEq(E.AddrT(E.NextAt(c,i)),E.AddrT a))) ->
          let a' = addr_to_tslk_addr a in
          let c' = cell_to_tslk_cell c in
          let i' = int_to_tslk_level i in
          SLK.addr_mark_smp_interesting a' true;
          SLK.eq_addr a' (SLK.NextAt(c',i'))
      (* Translation of literals of the form c' = updCellAddr(c, i, a) *)
      | E.Literal(E.Atom(E.Eq(E.CellT d,E.CellT(E.UpdCellAddr(c,i,a)))))
      | E.Literal(E.Atom(E.Eq(E.CellT(E.UpdCellAddr(c,i,a)),E.CellT d)))
      | E.Literal(E.NegAtom(E.InEq(E.CellT d,E.CellT(E.UpdCellAddr(c,i,a)))))
      | E.Literal(E.NegAtom(E.InEq(E.CellT(E.UpdCellAddr(c,i,a)),E.CellT d))) ->
          begin
            let d' = cell_to_tslk_cell d in
            let c' = cell_to_tslk_cell c in
            let i' = int_to_tslk_level i in
            let a' = addr_to_tslk_addr a in
            let xs = ref [SLK.eq_elem (SLK.CellData d') (SLK.CellData c')] in
            for n = 0 to (SLK.k-1) do
              let n' = SLK.LevelVal n in
              xs := (SLK.Implies
                      (SLK.eq_level i' n',
                       SLK.eq_addr (SLK.NextAt(d',n')) a')) ::
                    (SLK.Implies
                      (SLK.ineq_level i' n',
                       SLK.eq_addr (SLK.NextAt(d',n')) (SLK.NextAt(c',n')))) ::
                    (SLK.eq_tid (SLK.CellLockIdAt(d',n')) (SLK.CellLockIdAt(c',n'))) ::
                    (!xs)
            done;
            SLK.conj_list (!xs)
          end
      | E.Literal l       -> SLK.Literal (literal_to_tslk_literal l)
      | E.True            -> SLK.True
      | E.False           -> SLK.False
      | E.And (f1,f2)     -> SLK.And (to_formula f1, to_formula f2)
      | E.Or (f1,f2)      -> SLK.Or (to_formula f1, to_formula f2)
      | E.Not f1          -> SLK.Not (to_formula f1)
      | E.Implies (f1,f2) -> SLK.Implies (to_formula f1, to_formula f2)
      | E.Iff (f1,f2)     -> SLK.Iff (to_formula f1, to_formula f2)


    and formula_to_tslk_formula (phi:E.formula) : SLK.formula =
      formula_to_tslk_formula_aux (norm_to_tslk phi)



(* TSLKExpression to Expression conversion *)

    let sort_to_expr_sort (s:SLK.sort) : E.sort =
      match s with
      | SLK.Set     -> E.Set
      | SLK.Elem    -> E.Elem
      | SLK.Tid    -> E.Tid
      | SLK.Addr    -> E.Addr
      | SLK.Cell    -> E.Cell
      | SLK.SetTh   -> E.SetTh
      | SLK.SetElem -> E.SetElem
      | SLK.Path    -> E.Path
      | SLK.Mem     -> E.Mem
      | SLK.Level   -> E.Int
      | SLK.Bool    -> E.Bool
      | SLK.Unknown -> E.Unknown



    let rec var_to_expr_var (v:SLK.variable) : E.variable =
      E.build_var (SLK.var_id v)
                  (sort_to_expr_sort (SLK.var_sort v))
                  (SLK.var_is_primed v)
                  (shared_to_expr_shared (SLK.var_parameter v))
                  (scope_to_expr_scope (SLK.var_scope v))
                  (E.RealVar)

    and shared_to_expr_shared (th:SLK.shared_or_local) : E.shared_or_local =
      match th with
      | SLK.Shared  -> E.Shared
      | SLK.Local t -> E.Local (tid_to_expr_tid t)


    and scope_to_expr_scope (p:SLK.procedure_name) : E.procedure_name =
      match p with
      | SLK.GlobalScope -> E.GlobalScope
      | SLK.Scope proc  -> E.Scope proc
                      

    and tid_to_expr_tid (th:SLK.tid) : E.tid =
      match th with
      | SLK.VarTh v            -> E.VarTh (var_to_expr_var v)
      | SLK.NoTid             -> E.NoTid
      | SLK.CellLockIdAt (c,l) -> E.CellLockIdAt (cell_to_expr_cell c,
                                                     level_to_expr_int l)


    and term_to_expr_term (t:SLK.term) : E.term =
      match t with
      | SLK.VarT v             -> E.VarT (var_to_expr_var v)
      | SLK.SetT s             -> E.SetT (set_to_expr_set s)
      | SLK.ElemT e            -> E.ElemT (elem_to_expr_elem e)
      | SLK.TidT t            -> E.TidT (tid_to_expr_tid t)
      | SLK.AddrT a            -> E.AddrT (addr_to_expr_addr a)
      | SLK.CellT c            -> E.CellT (cell_to_expr_cell c)
      | SLK.SetThT st          -> E.SetThT (setth_to_expr_setth st)
      | SLK.SetElemT st        -> E.SetElemT (setelem_to_expr_setelem st)
      | SLK.PathT p            -> E.PathT (path_to_expr_path p)
      | SLK.MemT m             -> E.MemT (mem_to_expr_mem m)
      | SLK.LevelT i           -> E.IntT (level_to_expr_int i)
      | SLK.VarUpdate (v,th,t) ->
          let expr_a  = E.VarArray (var_to_expr_var v) in
          let expr_th = tid_to_expr_tid th in
          let expr_t  = E.Term (term_to_expr_term t)
          in
            E.ArrayT (E.ArrayUp (expr_a, expr_th, expr_t))


    and tsl_eq_to_eq ((t1,t2):SLK.eq) : E.eq =
      (term_to_expr_term t1, term_to_expr_term t2)


    and tsl_diseq_to_eq ((t1,t2):SLK.diseq) : E.diseq =
      (term_to_expr_term t1, term_to_expr_term t2)


    and set_to_expr_set (s:SLK.set) : E.set =
      let to_set = set_to_expr_set in
      match s with
      | SLK.VarSet v            -> E.VarSet (var_to_expr_var v)
      | SLK.EmptySet            -> E.EmptySet
      | SLK.Singl a             -> E.Singl (addr_to_expr_addr a)
      | SLK.Union (s1,s2)       -> E.Union (to_set s1, to_set s2)
      | SLK.Intr (s1,s2)        -> E.Intr (to_set s1, to_set s2)
      | SLK.Setdiff (s1,s2)     -> E.Setdiff (to_set s1, to_set s2)
      | SLK.PathToSet p         -> E.PathToSet (path_to_expr_path p)
      | SLK.AddrToSet (m,a,l)   -> E.AddrToSetAt (mem_to_expr_mem m,
                                                     addr_to_expr_addr a,
                                                     level_to_expr_int l)


    and elem_to_expr_elem (e:SLK.elem) : E.elem =
      match e with
      | SLK.VarElem v              -> E.VarElem (var_to_expr_var v)
      | SLK.CellData c             -> E.CellData (cell_to_expr_cell c)
      | SLK.HavocSkiplistElem      -> E.HavocSkiplistElem
      | SLK.LowestElem             -> E.LowestElem
      | SLK.HighestElem            -> E.HighestElem


    and addr_to_expr_addr (a:SLK.addr) : E.addr =
      match a with
      | SLK.VarAddr v              -> E.VarAddr (var_to_expr_var v)
      | SLK.Null                   -> E.Null
      | SLK.NextAt (c,l)           -> E.NextAt (cell_to_expr_cell c, level_to_expr_int l)
      | SLK.FirstLockedAt (m,p,i)  -> E.FirstLockedAt (mem_to_expr_mem m,
                                                           path_to_expr_path p,
                                                           level_to_expr_int i)


    and cell_to_expr_cell (c:SLK.cell) : E.cell =
      match c with
        SLK.VarCell v          -> E.VarCell (var_to_expr_var v)
      | SLK.Error              -> E.Error
      | SLK.MkCell (e,aa,tt)   -> E.MkSLKCell (elem_to_expr_elem e,
                                                   List.map addr_to_expr_addr aa,
                                                   List.map tid_to_expr_tid tt)
      | SLK.CellLockAt (c,l, t)-> E.CellLockAt (cell_to_expr_cell c,
                                                   level_to_expr_int l,
                                                   tid_to_expr_tid t)
      | SLK.CellUnlockAt (c,l) -> E.CellUnlockAt (cell_to_expr_cell c,
                                                     level_to_expr_int l)
      | SLK.CellAt (m,a)       -> E.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


    and setth_to_expr_setth (st:SLK.setth) : E.setth =
      let to_setth = setth_to_expr_setth in
      match st with
      | SLK.VarSetTh v        -> E.VarSetTh (var_to_expr_var v)
      | SLK.EmptySetTh        -> E.EmptySetTh
      | SLK.SinglTh t         -> E.SinglTh (tid_to_expr_tid t)
      | SLK.UnionTh (s1,s2)   -> E.UnionTh (to_setth s1, to_setth s2)
      | SLK.IntrTh (s1,s2)    -> E.IntrTh (to_setth s1, to_setth s2)
      | SLK.SetdiffTh (s1,s2) -> E.SetdiffTh (to_setth s1, to_setth s2)


    and setelem_to_expr_setelem (st:SLK.setelem) : E.setelem =
      let to_setelem = setelem_to_expr_setelem in
      match st with
      | SLK.VarSetElem v        -> E.VarSetElem (var_to_expr_var v)
      | SLK.EmptySetElem        -> E.EmptySetElem
      | SLK.SinglElem e         -> E.SinglElem (elem_to_expr_elem e)
      | SLK.UnionElem (s1,s2)   -> E.UnionElem (to_setelem s1, to_setelem s2)
      | SLK.IntrElem (s1,s2)    -> E.IntrElem (to_setelem s1, to_setelem s2)
      | SLK.SetdiffElem (s1,s2) -> E.SetdiffElem (to_setelem s1, to_setelem s2)
      | SLK.SetToElems (s,m)    -> E.SetToElems (set_to_expr_set s,
                                                    mem_to_expr_mem m)


    and path_to_expr_path (p:SLK.path) : E.path =
      match p with
      | SLK.VarPath v             -> E.VarPath (var_to_expr_var v)
      | SLK.Epsilon               -> E.Epsilon
      | SLK.SimplePath a          -> E.SimplePath (addr_to_expr_addr a)
      | SLK.GetPathAt (m,a1,a2,l) -> E.GetPathAt (mem_to_expr_mem m,
                                                      addr_to_expr_addr a1,
                                                      addr_to_expr_addr a2,
                                                      level_to_expr_int l)


    and mem_to_expr_mem (m:SLK.mem) : E.mem =
      match m with
      | SLK.VarMem v       -> E.VarMem (var_to_expr_var v)
      | SLK.Emp            -> raise(UnsupportedExpr(SLK.mem_to_str m))
      | SLK.Update (m,a,c) -> E.Update (mem_to_expr_mem m,
                                            addr_to_expr_addr a,
                                            cell_to_expr_cell c)


    and level_to_expr_int (i:SLK.level) : E.integer =
      match i with
      | SLK.LevelVal i     -> E.IntVal i
      | SLK.VarLevel v     -> E.VarInt (var_to_expr_var v)
      | SLK.LevelSucc i    -> E.IntAdd (level_to_expr_int i, E.IntVal 1)
      | SLK.LevelPred i    -> E.IntSub (level_to_expr_int i, E.IntVal 1)
      | SLK.HavocLevel     -> E.HavocLevel


    and atom_to_expr_atom (a:SLK.atom) : E.atom =
      let path    = path_to_expr_path       in
      let mem     = mem_to_expr_mem         in
      let addr    = addr_to_expr_addr       in
      let elem    = elem_to_expr_elem       in
      let set     = set_to_expr_set         in
      let tid     = tid_to_expr_tid         in
      let setth   = setth_to_expr_setth     in
      let setelem = setelem_to_expr_setelem in
      let integ   = level_to_expr_int       in
      let term    = term_to_expr_term       in
      match a with
        SLK.Append (p1,p2,p3)    -> E.Append (path p1,path p2,path p3)
      | SLK.Reach (m,a1,a2,l,p  )-> E.ReachAt (mem m, addr a1, addr a2,
                                                integ l, path p)
      | SLK.OrderList(m,a1,a2)   -> E.OrderList (mem m, addr a1, addr a2)
      | SLK.In (a,s)             -> E.In (addr a, set s)
      | SLK.SubsetEq (s1,s2)     -> E.SubsetEq (set s1, set s2)
      | SLK.InTh (t,s)           -> E.InTh (tid t, setth s)
      | SLK.SubsetEqTh (s1,s2)   -> E.SubsetEqTh (setth s1, setth s2)
      | SLK.InElem (e,s)         -> E.InElem (elem_to_expr_elem e, setelem s)
      | SLK.SubsetEqElem (s1,s2) -> E.SubsetEqElem (setelem s1, setelem s2)
      | SLK.Less (i1,i2)         -> E.Less (integ i1, integ i2)
      | SLK.Greater (i1,i2)      -> E.Greater (integ i1, integ i2)
      | SLK.LessEq (i1,i2)       -> E.LessEq (integ i1, integ i2)
      | SLK.GreaterEq (i1,i2)    -> E.GreaterEq (integ i1, integ i2)
      | SLK.LessElem (e1,e2)     -> E.LessElem (elem e1, elem e2)
      | SLK.GreaterElem (e1,e2)  -> E.GreaterElem (elem e1, elem e2)
      | SLK.Eq (t1,t2)           -> E.Eq (term t1, term t2)
      | SLK.InEq (t1,t2)         -> E.InEq (term t1, term t2)
      | SLK.BoolVar v            -> E.BoolVar (var_to_expr_var v)
      | SLK.PC (pc,t,pr)         -> E.PC (pc, shared_to_expr_shared t,pr)
      | SLK.PCUpdate (pc,t)      -> E.PCUpdate (pc, tid_to_expr_tid t)
      | SLK.PCRange (pc1,pc2,t,pr) -> E.PCRange (pc1, pc2, shared_to_expr_shared t, pr)


    and literal_to_expr_literal (l:SLK.literal) : E.literal =
      match l with
        SLK.Atom a    -> E.Atom (atom_to_expr_atom a)
      | SLK.NegAtom a -> E.NegAtom (atom_to_expr_atom a)


    and formula_to_expr_formula (f:SLK.formula) : E.formula =
      let to_formula = formula_to_expr_formula in
      match f with
        SLK.Literal l       -> E.Literal (literal_to_expr_literal l)
      | SLK.True            -> E.True
      | SLK.False           -> E.False
      | SLK.And (f1,f2)     -> E.And (to_formula f1, to_formula f2)
      | SLK.Or (f1,f2)      -> E.Or (to_formula f1, to_formula f2)
      | SLK.Not f1          -> E.Not (to_formula f1)
      | SLK.Implies (f1,f2) -> E.Implies (to_formula f1, to_formula f2)
      | SLK.Iff (f1,f2)     -> E.Iff (to_formula f1, to_formula f2)




  end
