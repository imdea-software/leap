open LeapLib



module Make (TSLK : TSLKExpression.S) =
  struct

    module Expr = Expression

    type varId = Expr.varId
    type sort  = Expr.sort
    type tid   = Expr.tid

    exception UnsupportedSort of string
    exception UnsupportedTSLKExpr of string
    exception UnsupportedExpr of string


    (* Expression to TSLKExpression conversion *)


    let rec sort_to_tslk_sort (s:Expr.sort) : TSLK.sort =
      match s with
        Expr.Set       -> TSLK.Set
      | Expr.Elem      -> TSLK.Elem
      | Expr.Thid      -> TSLK.Thid
      | Expr.Addr      -> TSLK.Addr
      | Expr.Cell      -> TSLK.Cell
      | Expr.SetTh     -> TSLK.SetTh
      | Expr.SetInt    -> RAISE(UnsupportedSort(Expr.sort_to_str s))
      | Expr.SetElem   -> TSLK.SetElem
      | Expr.Path      -> TSLK.Path
      | Expr.Mem       -> TSLK.Mem
      | Expr.Bool      -> TSLK.Bool
      | Expr.Int       -> TSLK.Level
      | Expr.Array     -> RAISE(UnsupportedSort(Expr.sort_to_str s))
      | Expr.AddrArray -> RAISE(UnsupportedSort(Expr.sort_to_str s))
      | Expr.TidArray  -> RAISE(UnsupportedSort(Expr.sort_to_str s))
      | Expr.Unknown   -> TSLK.Unknown


    and build_term_var (v:Expr.variable) : TSLK.term =
      let tslk_v = var_to_tslk_var v in
      match Expr.var_sort v with
        Expr.Set       -> TSLK.SetT       (TSLK.VarSet        tslk_v)
      | Expr.Elem      -> TSLK.ElemT      (TSLK.VarElem       tslk_v)
      | Expr.Thid      -> TSLK.ThidT      (TSLK.VarTh         tslk_v)
      | Expr.Addr      -> TSLK.AddrT      (TSLK.VarAddr       tslk_v)
      | Expr.Cell      -> TSLK.CellT      (TSLK.VarCell       tslk_v)
      | Expr.SetTh     -> TSLK.SetThT     (TSLK.VarSetTh      tslk_v)
      | Expr.Path      -> TSLK.PathT      (TSLK.VarPath       tslk_v)
      | Expr.Mem       -> TSLK.MemT       (TSLK.VarMem        tslk_v)
      | Expr.Int       -> TSLK.LevelT     (TSLK.VarLevel      tslk_v)
      | _              -> TSLK.VarT       (tslk_v)



    and var_to_tslk_var (v:Expr.variable) : TSLK.variable =
      let (id,s,pr,th,p,_) = v
      in
        (id, sort_to_tslk_sort s, pr, Option.lift tid_to_tslk_tid th, p)



    and tid_to_tslk_tid (th:Expr.tid) : TSLK.tid =
      match th with
        Expr.VarTh v            -> TSLK.VarTh (var_to_tslk_var v)
      | Expr.NoThid             -> TSLK.NoThid
      | Expr.CellLockId _       -> RAISE(UnsupportedTSLKExpr(Expr.tid_to_str th))
      | Expr.CellLockIdAt (c,l) -> TSLK.CellLockIdAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l)
      | Expr.ThidArrayRd _      -> RAISE(UnsupportedTSLKExpr(Expr.tid_to_str th))
      | Expr.ThidArrRd (tt,i)   -> RAISE(UnsupportedTSLKExpr(Expr.tid_to_str th))

    and term_to_tslk_term (t:Expr.term) : TSLK.term =
      match t with
        Expr.VarT v        -> TSLK.VarT (var_to_tslk_var v)
      | Expr.SetT s        -> TSLK.SetT (set_to_tslk_set s)
      | Expr.ElemT e       -> TSLK.ElemT (elem_to_tslk_elem e)
      | Expr.ThidT t       -> TSLK.ThidT (tid_to_tslk_tid t)
      | Expr.AddrT a       -> TSLK.AddrT (addr_to_tslk_addr a)
      | Expr.CellT c       -> TSLK.CellT (cell_to_tslk_cell c)
      | Expr.SetThT st     -> TSLK.SetThT (setth_to_tslk_setth st)
      | Expr.SetIntT _     -> RAISE(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.SetElemT st   -> TSLK.SetElemT (setelem_to_tslk_setelem st)
      | Expr.PathT p       -> TSLK.PathT (path_to_tslk_path p)
      | Expr.MemT m        -> TSLK.MemT (mem_to_tslk_mem m)
      | Expr.IntT i        -> TSLK.LevelT (int_to_tslk_level i)
      | Expr.AddrArrayT aa -> RAISE(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.TidArrayT tt  -> RAISE(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.ArrayT a      -> arrays_to_tslk_term a


    and arrays_to_tslk_term (a:Expr.arrays) : TSLK.term =
      match a with
      | Expr.VarArray v -> build_term_var v
      | Expr.ArrayUp (Expr.VarArray v,th_p,Expr.Term t) ->
          let tslk_v  = var_to_tslk_var v in
          let tslk_th = tid_to_tslk_tid th_p in
          let tslk_t  = term_to_tslk_term t
          in
            TSLK.VarUpdate (tslk_v, tslk_th, tslk_t)
      | Expr.ArrayUp (_,_,e) -> RAISE(UnsupportedTSLKExpr(Expr.expr_to_str e))


    and eq_to_tslk_eq ((t1,t2):Expr.eq) : TSLK.eq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


    and diseq_to_tslk_eq ((t1,t2):Expr.diseq) : TSLK.diseq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


    and set_to_tslk_set (s:Expr.set) : TSLK.set =
      let to_set = set_to_tslk_set in
      match s with
        Expr.VarSet v            -> TSLK.VarSet (var_to_tslk_var v)
      | Expr.EmptySet            -> TSLK.EmptySet
      | Expr.Singl a             -> TSLK.Singl (addr_to_tslk_addr a)
      | Expr.Union (s1,s2)       -> TSLK.Union (to_set s1, to_set s2)
      | Expr.Intr (s1,s2)        -> TSLK.Intr (to_set s1, to_set s2)
      | Expr.Setdiff (s1,s2)     -> TSLK.Setdiff (to_set s1, to_set s2)
      | Expr.PathToSet p         -> TSLK.PathToSet (path_to_tslk_path p)
      | Expr.AddrToSet _         -> RAISE(UnsupportedTSLKExpr(Expr.set_to_str s))
      | Expr.AddrToSetAt (m,a,l) -> TSLK.AddrToSet (mem_to_tslk_mem m,
                                                    addr_to_tslk_addr a,
                                                    int_to_tslk_level l)
      | Expr.SetArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSet (var_to_tslk_var v)
      | Expr.SetArrayRd _        -> RAISE(UnsupportedTSLKExpr(Expr.set_to_str s))


    and elem_to_tslk_elem (e:Expr.elem) : TSLK.elem =
      match e with
        Expr.VarElem v              -> TSLK.VarElem (var_to_tslk_var v)
      | Expr.CellData c             -> TSLK.CellData (cell_to_tslk_cell c)
      | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarElem (var_to_tslk_var v)
      | Expr.ElemArrayRd _          -> RAISE(UnsupportedTSLKExpr(Expr.elem_to_str e))
      | Expr.HavocListElem          -> RAISE(UnsupportedTSLKExpr(Expr.elem_to_str e))
      | Expr.HavocSkiplistElem      -> TSLK.HavocSkiplistElem
      | Expr.LowestElem             -> TSLK.LowestElem
      | Expr.HighestElem            -> TSLK.HighestElem


    and addr_to_tslk_addr (a:Expr.addr) : TSLK.addr =
      match a with
        Expr.VarAddr v              -> TSLK.VarAddr (var_to_tslk_var v)
      | Expr.Null                   -> TSLK.Null
      | Expr.Next _                 -> RAISE(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.NextAt (c,l)           -> TSLK.NextAt (cell_to_tslk_cell c, int_to_tslk_level l)
      | Expr.FirstLocked (m,p)      -> RAISE(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.FirstLockedAt (m,p,l)  -> TSLK.FirstLockedAt (mem_to_tslk_mem m,
                                                          path_to_tslk_path p,
                                                          int_to_tslk_level l)
      | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarAddr (var_to_tslk_var v)
      | Expr.AddrArrayRd _          -> RAISE(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.AddrArrRd (aa,i)       -> RAISE(UnsupportedTSLKExpr(Expr.addr_to_str a))


    and cell_to_tslk_cell (c:Expr.cell) : TSLK.cell =
      match c with
        Expr.VarCell v            -> TSLK.VarCell (var_to_tslk_var v)
      | Expr.Error                -> TSLK.Error
      | Expr.MkCell _             -> RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.MkSLKCell (e,aa,tt)  ->
          if List.length aa > TSLK.k || List.length tt > TSLK.k then
            begin
              Interface.Err.msg "Too many addresses or threads ids in MkCell" $
                Printf.sprintf "Tried to build a term:\n%s\n while in TSLK[%i]. \
                                Notice the number of addresses or threads identifiers \
                                exceeds the parameter of the theory."
                                (Expr.cell_to_str c) TSLK.k;
              RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))
            end
          else
            let aa_pad = LeapLib.list_of (TSLK.k - List.length aa) TSLK.Null in
            let tt_pad = LeapLib.list_of (TSLK.k - List.length tt) TSLK.NoThid in
            TSLK.MkCell (elem_to_tslk_elem e,
                         (List.map addr_to_tslk_addr aa) @ aa_pad,
                         (List.map tid_to_tslk_tid tt) @ tt_pad)
      | Expr.MkSLCell (e,aa,tt,l) -> RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))
      (* TSLK receives two arguments, while current epxression receives only one *)
      (* However, for the list examples, I think we will not need it *)
      | Expr.CellLock _           -> RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.CellLockAt (c,l,t)   -> TSLK.CellLockAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l,
                                                     tid_to_tslk_tid t)
      | Expr.CellUnlock _         -> RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.CellUnlockAt (c,l)   -> TSLK.CellUnlockAt (cell_to_tslk_cell c,
                                                       int_to_tslk_level l)
      | Expr.CellAt (m,a)         -> TSLK.CellAt (mem_to_tslk_mem m, addr_to_tslk_addr a)
      | Expr.CellArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarCell (var_to_tslk_var v)
      | Expr.CellArrayRd _        -> RAISE(UnsupportedTSLKExpr(Expr.cell_to_str c))


    and setth_to_tslk_setth (st:Expr.setth) : TSLK.setth =
      let to_setth = setth_to_tslk_setth in
      match st with
        Expr.VarSetTh v        -> TSLK.VarSetTh (var_to_tslk_var v)
      | Expr.EmptySetTh        -> TSLK.EmptySetTh
      | Expr.SinglTh t         -> TSLK.SinglTh (tid_to_tslk_tid t)
      | Expr.UnionTh (s1,s2)   -> TSLK.UnionTh (to_setth s1, to_setth s2)
      | Expr.IntrTh (s1,s2)    -> TSLK.IntrTh (to_setth s1, to_setth s2)
      | Expr.SetdiffTh (s1,s2) -> TSLK.SetdiffTh (to_setth s1, to_setth s2)
      | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSetTh (var_to_tslk_var v)
      | Expr.SetThArrayRd _    -> RAISE(UnsupportedTSLKExpr(Expr.setth_to_str st))


    and setelem_to_tslk_setelem (st:Expr.setelem) : TSLK.setelem =
      let to_setelem = setelem_to_tslk_setelem in
      match st with
        Expr.VarSetElem v        -> TSLK.VarSetElem (var_to_tslk_var v)
      | Expr.EmptySetElem        -> TSLK.EmptySetElem
      | Expr.SinglElem e         -> TSLK.SinglElem (elem_to_tslk_elem e)
      | Expr.UnionElem (s1,s2)   -> TSLK.UnionElem (to_setelem s1, to_setelem s2)
      | Expr.IntrElem (s1,s2)    -> TSLK.IntrElem (to_setelem s1, to_setelem s2)
      | Expr.SetdiffElem (s1,s2) -> TSLK.SetdiffElem (to_setelem s1, to_setelem s2)
      | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSetElem (var_to_tslk_var v)
      | Expr.SetToElems (s,m)    -> TSLK.SetToElems (set_to_tslk_set s,
                                                    mem_to_tslk_mem m)
      | Expr.SetElemArrayRd _    -> RAISE(UnsupportedTSLKExpr(Expr.setelem_to_str st))


    and path_to_tslk_path (p:Expr.path) : TSLK.path =
      match p with
        Expr.VarPath v             -> TSLK.VarPath (var_to_tslk_var v)
      | Expr.Epsilon               -> TSLK.Epsilon
      | Expr.SimplePath a          -> TSLK.SimplePath (addr_to_tslk_addr a)
      | Expr.GetPath _             -> RAISE(UnsupportedTSLKExpr(Expr.path_to_str p))
      | Expr.GetPathAt (m,a1,a2,l) -> TSLK.GetPathAt (mem_to_tslk_mem m,
                                                      addr_to_tslk_addr a1,
                                                      addr_to_tslk_addr a2,
                                                      int_to_tslk_level l)
      | Expr.PathArrayRd _         -> RAISE(UnsupportedTSLKExpr(Expr.path_to_str p))


    and mem_to_tslk_mem (m:Expr.mem) : TSLK.mem =
      match m with
        Expr.VarMem v       -> TSLK.VarMem (var_to_tslk_var v)
      | Expr.Update (m,a,c) -> TSLK.Update (mem_to_tslk_mem m,
                                           addr_to_tslk_addr a,
                                           cell_to_tslk_cell c)
      (* Missing the case for "emp" *)
      | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarMem (var_to_tslk_var v)
      | Expr.MemArrayRd _        -> RAISE(UnsupportedTSLKExpr(Expr.mem_to_str m))


    and int_to_tslk_level (i:Expr.integer) : TSLK.level =
      let rec apply n f x = if n <= 1 then f x else apply (n-1) f (f x) in
      let succ = (fun x -> TSLK.LevelSucc x) in
      let pred = (fun x -> TSLK.LevelPred x) in
      let tolevel = int_to_tslk_level in
      match i with
        Expr.IntVal l       -> if l < 0 || TSLK.k <= l then
                                 begin
                                   Interface.Err.msg "Level out of bounds" $
                                   Printf.sprintf "Level %i is out of the bounds of TSLK[%i], \
                                                   which goes from 0 to %i."
                                      l TSLK.k (TSLK.k-1);
                                   RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
                                 end
                               else
                                 TSLK.LevelVal l
      | Expr.VarInt v       -> TSLK.VarLevel (var_to_tslk_var v)
      | Expr.IntNeg i       -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntAdd (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (Expr.IntVal j1, Expr.IntVal j2) -> TSLK.LevelVal (j1+j2)
                                 | (Expr.VarInt v , Expr.IntVal j ) -> apply j succ (tolevel i1)
                                 | (Expr.IntVal j , Expr.VarInt v ) -> apply j succ (tolevel i2)
                                 | _ -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
                               end
      | Expr.IntSub (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (Expr.IntVal j1, Expr.IntVal j2) -> TSLK.LevelVal (j1-j2)
                                 | (Expr.VarInt v , Expr.IntVal j ) -> apply j pred (tolevel i1)
                                 | _ -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
                               end
      | Expr.IntMul (i1,i2) -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntDiv (i1,i2) -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.CellMax (c)    -> TSLK.LevelVal TSLK.k
      | Expr.IntArrayRd _   -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntSetMin _    -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntSetMax _    -> RAISE(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.HavocLevel     -> TSLK.HavocLevel


    and atom_to_tslk_atom (a:Expr.atom) : TSLK.atom =
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
        Expr.Append (p1,p2,p3)    -> TSLK.Append (path p1,path p2,path p3)
      | Expr.Reach _              -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.ReachAt (m,a1,a2,l,p)-> TSLK.Reach (mem m, addr a1, addr a2, integ l, path p)
      | Expr.OrderList(m,a1,a2)   -> TSLK.OrderList (mem m, addr a1, addr a2)
      | Expr.Skiplist _           -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.In (a,s)             -> TSLK.In (addr a, set s)
      | Expr.SubsetEq (s1,s2)     -> TSLK.SubsetEq (set s1, set s2)
      | Expr.InTh (t,s)           -> TSLK.InTh (tid t, setth s)
      | Expr.SubsetEqTh (s1,s2)   -> TSLK.SubsetEqTh (setth s1, setth s2)
      | Expr.InInt _              -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.SubsetEqInt _        -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.InElem (e,s)         -> TSLK.InElem (elem_to_tslk_elem e, setelem s)
      | Expr.SubsetEqElem (s1,s2) -> TSLK.SubsetEqElem (setelem s1, setelem s2)
      | Expr.Less (i1,i2)         -> TSLK.Less (integ i1, integ i2)
      | Expr.Greater (i1,i2)      -> TSLK.Greater (integ i1, integ i2)
      | Expr.LessEq (i1,i2)       -> TSLK.LessEq (integ i1, integ i2)
      | Expr.GreaterEq (i1,i2)    -> TSLK.GreaterEq (integ i1, integ i2)
      | Expr.LessTid _            -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.LessElem (e1,e2)     -> TSLK.LessElem (elem e1, elem e2)
      | Expr.GreaterElem (e1,e2)  -> TSLK.GreaterElem (elem e1, elem e2)
      | Expr.Eq (t1,t2)           -> TSLK.Eq (term t1, term t2)
      | Expr.InEq (t1,t2)         -> TSLK.InEq (term t1, term t2)
      | Expr.BoolVar v            -> TSLK.BoolVar (var_to_tslk_var v)
      | Expr.BoolArrayRd _        -> RAISE(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.PC (pc,t,pr)         -> TSLK.PC (pc, Option.lift tid_to_tslk_tid t,pr)
      | Expr.PCUpdate (pc,t)      -> TSLK.PCUpdate (pc, tid_to_tslk_tid t)
      | Expr.PCRange (pc1,pc2,t,pr) -> TSLK.PCRange (pc1, pc2,
                                            Option.lift tid_to_tslk_tid t,pr)


    and literal_to_tslk_literal (l:Expr.literal) : TSLK.literal =
      match l with
        Expr.Atom a    -> TSLK.Atom (atom_to_tslk_atom a)
      | Expr.NegAtom a -> TSLK.NegAtom (atom_to_tslk_atom a)


    and formula_to_tslk_formula (f:Expr.formula) : TSLK.formula =
      LOG "Entering formula_to_tslk_formula..." LEVEL TRACE;
      let to_formula = formula_to_tslk_formula in
      match f with
        Expr.Literal l       -> TSLK.Literal (literal_to_tslk_literal l)
      | Expr.True            -> TSLK.True
      | Expr.False           -> TSLK.False
      | Expr.And (f1,f2)     -> TSLK.And (to_formula f1, to_formula f2)
      | Expr.Or (f1,f2)      -> TSLK.Or (to_formula f1, to_formula f2)
      | Expr.Not f1          -> TSLK.Not (to_formula f1)
      | Expr.Implies (f1,f2) -> TSLK.Implies (to_formula f1, to_formula f2)
      | Expr.Iff (f1,f2)     -> TSLK.Iff (to_formula f1, to_formula f2)




(* TSLKExpression to Expression conversion *)

    let sort_to_expr_sort (s:TSLK.sort) : Expr.sort =
      match s with
      | TSLK.Set     -> Expr.Set
      | TSLK.Elem    -> Expr.Elem
      | TSLK.Thid    -> Expr.Thid
      | TSLK.Addr    -> Expr.Addr
      | TSLK.Cell    -> Expr.Cell
      | TSLK.SetTh   -> Expr.SetTh
      | TSLK.SetElem -> Expr.SetElem
      | TSLK.Path    -> Expr.Path
      | TSLK.Mem     -> Expr.Mem
      | TSLK.Level   -> Expr.Int
      | TSLK.Bool    -> Expr.Bool
      | TSLK.Unknown -> Expr.Unknown



    let rec var_to_expr_var (v:TSLK.variable) : Expr.variable =
      let (id,s,pr,th,p) = v
      in
        (id, sort_to_expr_sort s, pr, Option.lift tid_to_expr_tid th, p, Expr.Normal)



    and tid_to_expr_tid (th:TSLK.tid) : Expr.tid =
      match th with
      | TSLK.VarTh v            -> Expr.VarTh (var_to_expr_var v)
      | TSLK.NoThid             -> Expr.NoThid
      | TSLK.CellLockIdAt (c,l) -> Expr.CellLockIdAt (cell_to_expr_cell c,
                                                     level_to_expr_int l)


    and term_to_expr_term (t:TSLK.term) : Expr.term =
      match t with
      | TSLK.VarT v             -> Expr.VarT (var_to_expr_var v)
      | TSLK.SetT s             -> Expr.SetT (set_to_expr_set s)
      | TSLK.ElemT e            -> Expr.ElemT (elem_to_expr_elem e)
      | TSLK.ThidT t            -> Expr.ThidT (tid_to_expr_tid t)
      | TSLK.AddrT a            -> Expr.AddrT (addr_to_expr_addr a)
      | TSLK.CellT c            -> Expr.CellT (cell_to_expr_cell c)
      | TSLK.SetThT st          -> Expr.SetThT (setth_to_expr_setth st)
      | TSLK.SetElemT st        -> Expr.SetElemT (setelem_to_expr_setelem st)
      | TSLK.PathT p            -> Expr.PathT (path_to_expr_path p)
      | TSLK.MemT m             -> Expr.MemT (mem_to_expr_mem m)
      | TSLK.LevelT i           -> Expr.IntT (level_to_expr_int i)
      | TSLK.VarUpdate (v,th,t) ->
          let expr_a  = Expr.VarArray (var_to_expr_var v) in
          let expr_th = tid_to_expr_tid th in
          let expr_t  = Expr.Term (term_to_expr_term t)
          in
            Expr.ArrayT (Expr.ArrayUp (expr_a, expr_th, expr_t))


    and tsl_eq_to_eq ((t1,t2):TSLK.eq) : Expr.eq =
      (term_to_expr_term t1, term_to_expr_term t2)


    and tsl_diseq_to_eq ((t1,t2):TSLK.diseq) : Expr.diseq =
      (term_to_expr_term t1, term_to_expr_term t2)


    and set_to_expr_set (s:TSLK.set) : Expr.set =
      let to_set = set_to_expr_set in
      match s with
      | TSLK.VarSet v            -> Expr.VarSet (var_to_expr_var v)
      | TSLK.EmptySet            -> Expr.EmptySet
      | TSLK.Singl a             -> Expr.Singl (addr_to_expr_addr a)
      | TSLK.Union (s1,s2)       -> Expr.Union (to_set s1, to_set s2)
      | TSLK.Intr (s1,s2)        -> Expr.Intr (to_set s1, to_set s2)
      | TSLK.Setdiff (s1,s2)     -> Expr.Setdiff (to_set s1, to_set s2)
      | TSLK.PathToSet p         -> Expr.PathToSet (path_to_expr_path p)
      | TSLK.AddrToSet (m,a,l)   -> Expr.AddrToSetAt (mem_to_expr_mem m,
                                                     addr_to_expr_addr a,
                                                     level_to_expr_int l)


    and elem_to_expr_elem (e:TSLK.elem) : Expr.elem =
      match e with
      | TSLK.VarElem v              -> Expr.VarElem (var_to_expr_var v)
      | TSLK.CellData c             -> Expr.CellData (cell_to_expr_cell c)
      | TSLK.HavocSkiplistElem      -> Expr.HavocSkiplistElem
      | TSLK.LowestElem             -> Expr.LowestElem
      | TSLK.HighestElem            -> Expr.HighestElem


    and addr_to_expr_addr (a:TSLK.addr) : Expr.addr =
      match a with
      | TSLK.VarAddr v              -> Expr.VarAddr (var_to_expr_var v)
      | TSLK.Null                   -> Expr.Null
      | TSLK.NextAt (c,l)           -> Expr.NextAt (cell_to_expr_cell c, level_to_expr_int l)
      | TSLK.FirstLockedAt (m,p,i)  -> Expr.FirstLockedAt (mem_to_expr_mem m,
                                                           path_to_expr_path p,
                                                           level_to_expr_int i)


    and cell_to_expr_cell (c:TSLK.cell) : Expr.cell =
      match c with
        TSLK.VarCell v          -> Expr.VarCell (var_to_expr_var v)
      | TSLK.Error              -> Expr.Error
      | TSLK.MkCell (e,aa,tt)   -> Expr.MkSLKCell (elem_to_expr_elem e,
                                                   List.map addr_to_expr_addr aa,
                                                   List.map tid_to_expr_tid tt)
      | TSLK.CellLockAt (c,l, t)-> Expr.CellLockAt (cell_to_expr_cell c,
                                                   level_to_expr_int l,
                                                   tid_to_expr_tid t)
      | TSLK.CellUnlockAt (c,l) -> Expr.CellUnlockAt (cell_to_expr_cell c,
                                                     level_to_expr_int l)
      | TSLK.CellAt (m,a)       -> Expr.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


    and setth_to_expr_setth (st:TSLK.setth) : Expr.setth =
      let to_setth = setth_to_expr_setth in
      match st with
      | TSLK.VarSetTh v        -> Expr.VarSetTh (var_to_expr_var v)
      | TSLK.EmptySetTh        -> Expr.EmptySetTh
      | TSLK.SinglTh t         -> Expr.SinglTh (tid_to_expr_tid t)
      | TSLK.UnionTh (s1,s2)   -> Expr.UnionTh (to_setth s1, to_setth s2)
      | TSLK.IntrTh (s1,s2)    -> Expr.IntrTh (to_setth s1, to_setth s2)
      | TSLK.SetdiffTh (s1,s2) -> Expr.SetdiffTh (to_setth s1, to_setth s2)


    and setelem_to_expr_setelem (st:TSLK.setelem) : Expr.setelem =
      let to_setelem = setelem_to_expr_setelem in
      match st with
      | TSLK.VarSetElem v        -> Expr.VarSetElem (var_to_expr_var v)
      | TSLK.EmptySetElem        -> Expr.EmptySetElem
      | TSLK.SinglElem e         -> Expr.SinglElem (elem_to_expr_elem e)
      | TSLK.UnionElem (s1,s2)   -> Expr.UnionElem (to_setelem s1, to_setelem s2)
      | TSLK.IntrElem (s1,s2)    -> Expr.IntrElem (to_setelem s1, to_setelem s2)
      | TSLK.SetdiffElem (s1,s2) -> Expr.SetdiffElem (to_setelem s1, to_setelem s2)
      | TSLK.SetToElems (s,m)    -> Expr.SetToElems (set_to_expr_set s,
                                                    mem_to_expr_mem m)


    and path_to_expr_path (p:TSLK.path) : Expr.path =
      match p with
      | TSLK.VarPath v             -> Expr.VarPath (var_to_expr_var v)
      | TSLK.Epsilon               -> Expr.Epsilon
      | TSLK.SimplePath a          -> Expr.SimplePath (addr_to_expr_addr a)
      | TSLK.GetPathAt (m,a1,a2,l) -> Expr.GetPathAt (mem_to_expr_mem m,
                                                      addr_to_expr_addr a1,
                                                      addr_to_expr_addr a2,
                                                      level_to_expr_int l)


    and mem_to_expr_mem (m:TSLK.mem) : Expr.mem =
      match m with
      | TSLK.VarMem v       -> Expr.VarMem (var_to_expr_var v)
      | TSLK.Emp            -> RAISE(UnsupportedExpr(TSLK.mem_to_str m))
      | TSLK.Update (m,a,c) -> Expr.Update (mem_to_expr_mem m,
                                            addr_to_expr_addr a,
                                            cell_to_expr_cell c)


    and level_to_expr_int (i:TSLK.level) : Expr.integer =
      match i with
      | TSLK.LevelVal i     -> Expr.IntVal i
      | TSLK.VarLevel v     -> Expr.VarInt (var_to_expr_var v)
      | TSLK.LevelSucc i    -> Expr.IntAdd (level_to_expr_int i, Expr.IntVal 1)
      | TSLK.LevelPred i    -> Expr.IntSub (level_to_expr_int i, Expr.IntVal 1)
      | TSLK.HavocLevel     -> Expr.HavocLevel


    and atom_to_expr_atom (a:TSLK.atom) : Expr.atom =
      let path    = path_to_expr_path       in
      let mem     = mem_to_expr_mem         in
      let addr    = addr_to_expr_addr       in
      let elem    = elem_to_expr_elem       in
      let set     = set_to_expr_set         in
      let tid     = tid_to_expr_tid         in
      let setth   = setth_to_expr_setth     in
      let setelem = setelem_to_expr_setelem in
      let integ   = level_to_expr_int         in
      let term    = term_to_expr_term       in
      match a with
        TSLK.Append (p1,p2,p3)    -> Expr.Append (path p1,path p2,path p3)
      | TSLK.Reach (m,a1,a2,l,p  )-> Expr.ReachAt (mem m, addr a1, addr a2,
                                                integ l, path p)
      | TSLK.OrderList(m,a1,a2)   -> Expr.OrderList (mem m, addr a1, addr a2)
      | TSLK.In (a,s)             -> Expr.In (addr a, set s)
      | TSLK.SubsetEq (s1,s2)     -> Expr.SubsetEq (set s1, set s2)
      | TSLK.InTh (t,s)           -> Expr.InTh (tid t, setth s)
      | TSLK.SubsetEqTh (s1,s2)   -> Expr.SubsetEqTh (setth s1, setth s2)
      | TSLK.InElem (e,s)         -> Expr.InElem (elem_to_expr_elem e, setelem s)
      | TSLK.SubsetEqElem (s1,s2) -> Expr.SubsetEqElem (setelem s1, setelem s2)
      | TSLK.Less (i1,i2)         -> Expr.Less (integ i1, integ i2)
      | TSLK.Greater (i1,i2)      -> Expr.Greater (integ i1, integ i2)
      | TSLK.LessEq (i1,i2)       -> Expr.LessEq (integ i1, integ i2)
      | TSLK.GreaterEq (i1,i2)    -> Expr.GreaterEq (integ i1, integ i2)
      | TSLK.LessElem (e1,e2)     -> Expr.LessElem (elem e1, elem e2)
      | TSLK.GreaterElem (e1,e2)  -> Expr.GreaterElem (elem e1, elem e2)
      | TSLK.Eq (t1,t2)           -> Expr.Eq (term t1, term t2)
      | TSLK.InEq (t1,t2)         -> Expr.InEq (term t1, term t2)
      | TSLK.BoolVar v            -> Expr.BoolVar (var_to_expr_var v)
      | TSLK.PC (pc,t,pr)         -> Expr.PC (pc, Option.lift tid_to_expr_tid t,pr)
      | TSLK.PCUpdate (pc,t)      -> Expr.PCUpdate (pc, tid_to_expr_tid t)
      | TSLK.PCRange (pc1,pc2,t,pr) -> Expr.PCRange (pc1, pc2,
                                            Option.lift tid_to_expr_tid t,pr)


    and literal_to_expr_literal (l:TSLK.literal) : Expr.literal =
      match l with
        TSLK.Atom a    -> Expr.Atom (atom_to_expr_atom a)
      | TSLK.NegAtom a -> Expr.NegAtom (atom_to_expr_atom a)


    and formula_to_expr_formula (f:TSLK.formula) : Expr.formula =
      let to_formula = formula_to_expr_formula in
      match f with
        TSLK.Literal l       -> Expr.Literal (literal_to_expr_literal l)
      | TSLK.True            -> Expr.True
      | TSLK.False           -> Expr.False
      | TSLK.And (f1,f2)     -> Expr.And (to_formula f1, to_formula f2)
      | TSLK.Or (f1,f2)      -> Expr.Or (to_formula f1, to_formula f2)
      | TSLK.Not f1          -> Expr.Not (to_formula f1)
      | TSLK.Implies (f1,f2) -> Expr.Implies (to_formula f1, to_formula f2)
      | TSLK.Iff (f1,f2)     -> Expr.Iff (to_formula f1, to_formula f2)




  end
