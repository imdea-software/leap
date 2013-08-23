open LeapLib



module Make (SLK : TSLKExpression.S) =
  struct

    module E = Expression

    type varId = E.varId
    type sort  = E.sort
    type tid   = E.tid

    exception UnsupportedSort of string
    exception UnsupportedTSLKExpr of string
    exception UnsupportedExpr of string


    (* Expression to TSLKExpression conversion *)


    let rec sort_to_tslk_sort (s:E.sort) : SLK.sort =
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
      | E.NoTid             -> SLK.NoTid
      | E.CellLockId _       -> raise(UnsupportedTSLKExpr(E.tid_to_str th))
      | E.CellLockIdAt (c,l) -> SLK.CellLockIdAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l)
      | E.TidArrayRd _      -> raise(UnsupportedTSLKExpr(E.tid_to_str th))
      | E.TidArrRd (tt,i)   -> raise(UnsupportedTSLKExpr(E.tid_to_str th))

    and term_to_tslk_term (t:E.term) : SLK.term =
      match t with
        E.VarT v        -> SLK.VarT (var_to_tslk_var v)
      | E.SetT s        -> SLK.SetT (set_to_tslk_set s)
      | E.ElemT e       -> SLK.ElemT (elem_to_tslk_elem e)
      | E.TidT t       -> SLK.TidT (tid_to_tslk_tid t)
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


    and eq_to_tslk_eq ((t1,t2):E.eq) : SLK.eq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


    and diseq_to_tslk_eq ((t1,t2):E.diseq) : SLK.diseq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


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
        E.IntVal l       -> if l < 0 || SLK.k <= l then
                                 begin
                                   Interface.Err.msg "Level out of bounds" $
                                   Printf.sprintf "Level %i is out of the bounds of TSLK[%i], \
                                                   which goes from 0 to %i."
                                      l SLK.k (SLK.k-1);
                                   raise(UnsupportedTSLKExpr(E.integer_to_str i))
                                 end
                               else
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


    and formula_to_tslk_formula (f:E.formula) : SLK.formula =
(*      LOG "Entering formula_to_tslk_formula..." LEVEL TRACE; *)
      let to_formula = formula_to_tslk_formula in
      match f with
        E.Literal l       -> SLK.Literal (literal_to_tslk_literal l)
      | E.True            -> SLK.True
      | E.False           -> SLK.False
      | E.And (f1,f2)     -> SLK.And (to_formula f1, to_formula f2)
      | E.Or (f1,f2)      -> SLK.Or (to_formula f1, to_formula f2)
      | E.Not f1          -> SLK.Not (to_formula f1)
      | E.Implies (f1,f2) -> SLK.Implies (to_formula f1, to_formula f2)
      | E.Iff (f1,f2)     -> SLK.Iff (to_formula f1, to_formula f2)




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
