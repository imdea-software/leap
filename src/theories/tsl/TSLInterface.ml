open LeapLib

module E=Expression
module SL=TSLExpression


type varId = E.varId
type sort  = E.sort
type tid   = E.tid

exception UnsupportedSort of string
exception UnsupportedTslExpr of string



(* Expression to TslExpression conversion *)


let rec sort_to_tsl_sort (s:E.sort) : SL.sort =
(*  LOG "Entering sort_to_tsl_sort..." LEVEL TRACE; *)
(*  LOG "sort_to_tsl_sort(%s)" (E.sort_to_str s) LEVEL DEBUG; *)
  match s with
    E.Set       -> SL.Set
  | E.Elem      -> SL.Elem
  | E.Tid      -> SL.Tid
  | E.Addr      -> SL.Addr
  | E.Cell      -> SL.Cell
  | E.SetTh     -> SL.SetTh
  | E.SetInt    -> raise(UnsupportedSort(E.sort_to_str s))
  | E.SetElem   -> SL.SetElem
  | E.Path      -> SL.Path
  | E.Mem       -> SL.Mem
  | E.Bool      -> SL.Bool
  | E.Int       -> SL.Int
  | E.Array     -> raise(UnsupportedSort(E.sort_to_str s))
  | E.AddrArray -> SL.AddrArray
  | E.TidArray  -> SL.TidArray
  | E.Unknown   -> SL.Unknown



and build_term_var (v:E.variable) : SL.term =
(*  LOG "Entering build_term_var..." LEVEL TRACE; *)
(*  LOG "build_term_var(%s)" (E.variable_to_str v) LEVEL DEBUG; *)
  let tsl_v = var_to_tsl_var v in
  match (E.var_sort v) with
    E.Set       -> SL.SetT       (SL.VarSet        tsl_v)
  | E.Elem      -> SL.ElemT      (SL.VarElem       tsl_v)
  | E.Tid      -> SL.TidT      (SL.VarTh         tsl_v)
  | E.Addr      -> SL.AddrT      (SL.VarAddr       tsl_v)
  | E.Cell      -> SL.CellT      (SL.VarCell       tsl_v)
  | E.SetTh     -> SL.SetThT     (SL.VarSetTh      tsl_v)
  | E.Path      -> SL.PathT      (SL.VarPath       tsl_v)
  | E.Mem       -> SL.MemT       (SL.VarMem        tsl_v)
  | E.Int       -> SL.IntT       (SL.VarInt        tsl_v)
  | E.AddrArray -> SL.AddrArrayT (SL.VarAddrArray  tsl_v)
  | E.TidArray  -> SL.TidArrayT  (SL.VarTidArray   tsl_v)
  | _              -> SL.VarT       (tsl_v)



and var_to_tsl_var (v:E.variable) : SL.variable =
(*  LOG "Entering var_to_tsl_var..." LEVEL TRACE; *)
(*  LOG "var_to_tsl_var(%s)" (E.variable_to_str v) LEVEL DEBUG; *)
  SL.build_var (E.var_id v)
               (sort_to_tsl_sort (E.var_sort v))
               (E.var_is_primed v)
               (shared_to_tsl_shared (E.var_parameter v))
               (scope_to_tsl_scope (E.var_scope v))


and shared_to_tsl_shared (th:E.shared_or_local) : SL.shared_or_local =
  match th with
  | E.Shared  -> SL.Shared
  | E.Local t -> SL.Local (tid_to_tsl_tid t)


and scope_to_tsl_scope (p:E.procedure_name) : SL.procedure_name =
  match p with
  | E.GlobalScope -> SL.GlobalScope
  | E.Scope proc  -> SL.Scope proc


and tid_to_tsl_tid (th:E.tid) : SL.tid =
(*  LOG "Entering tid_to_tsl_tid..." LEVEL TRACE; *)
(*  LOG "tid_to_tsl_tid(%s)" (E.tid_to_str th) LEVEL DEBUG; *)
  match th with
    E.VarTh v            -> SL.VarTh (var_to_tsl_var v)
  | E.NoTid             -> SL.NoTid
  | E.CellLockId _       -> raise(UnsupportedTslExpr(E.tid_to_str th))
  | E.CellLockIdAt (c,l) -> SL.CellLockIdAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l)
  | E.TidArrayRd _      -> raise(UnsupportedTslExpr(E.tid_to_str th))
  | E.TidArrRd (tt,i)   -> SL.TidArrRd (tidarr_to_tsl_tidarr tt,
                                              int_to_tsl_int i)

and term_to_tsl_term (t:E.term) : SL.term =
(*  LOG "Entering term_to_tsl_term..." LEVEL TRACE; *)
(*  LOG "term_to_tsl_term(%s)" (E.term_to_str t) LEVEL DEBUG; *)
  match t with
    E.VarT v        -> SL.VarT (var_to_tsl_var v)
  | E.SetT s        -> SL.SetT (set_to_tsl_set s)
  | E.ElemT e       -> SL.ElemT (elem_to_tsl_elem e)
  | E.TidT t       -> SL.TidT (tid_to_tsl_tid t)
  | E.AddrT a       -> SL.AddrT (addr_to_tsl_addr a)
  | E.CellT c       -> SL.CellT (cell_to_tsl_cell c)
  | E.SetThT st     -> SL.SetThT (setth_to_tsl_setth st)
  | E.SetIntT _     -> raise(UnsupportedTslExpr(E.term_to_str t))
  | E.SetElemT st   -> SL.SetElemT (setelem_to_tsl_setelem st)
  | E.PathT p       -> SL.PathT (path_to_tsl_path p)
  | E.MemT m        -> SL.MemT (mem_to_tsl_mem m)
  | E.IntT i        -> SL.IntT (int_to_tsl_int i)
  | E.AddrArrayT aa -> SL.AddrArrayT (addrarr_to_tsl_addrarr aa)
  | E.TidArrayT tt  -> SL.TidArrayT (tidarr_to_tsl_tidarr tt)
  | E.ArrayT a      -> arrays_to_tsl_term a


and arrays_to_tsl_term (a:E.arrays) : SL.term =
  match a with
  | E.VarArray v -> build_term_var v
  | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
      let tsl_v  = var_to_tsl_var v in
      let tsl_th = tid_to_tsl_tid th_p in
      let tsl_t  = term_to_tsl_term t
      in
        SL.VarUpdate (tsl_v, tsl_th, tsl_t)
  | E.ArrayUp (_,_,e) -> raise(UnsupportedTslExpr(E.expr_to_str e))


and eq_to_tsl_eq ((t1,t2):E.eq) : SL.eq =
(*  LOG "Entering eq_to_tsl_eq..." LEVEL TRACE; *)
(*  LOG "eq_to_tsl_eq(%s,%s)" (E.term_to_str t1) *)
(*                            (E.term_to_str t2) LEVEL DEBUG; *)
  (term_to_tsl_term t1, term_to_tsl_term t2)


and diseq_to_tsl_diseq ((t1,t2):E.diseq) : SL.diseq =
(*  LOG "Entering diseq_to_tsl_diseq..." LEVEL TRACE; *)
(*  LOG "diseq_to_tsl_diseq(%s,%s)" (E.term_to_str t1) *)
(*                                  (E.term_to_str t2) LEVEL DEBUG; *)
  (term_to_tsl_term t1, term_to_tsl_term t2)


and set_to_tsl_set (s:E.set) : SL.set =
(*  LOG "Entering set_to_tsl_set..." LEVEL TRACE; *)
(*  LOG "set_to_tsl_set(%s)" (E.set_to_str s) LEVEL DEBUG; *)
  let to_set = set_to_tsl_set in
  match s with
    E.VarSet v            -> SL.VarSet (var_to_tsl_var v)
  | E.EmptySet            -> SL.EmptySet
  | E.Singl a             -> SL.Singl (addr_to_tsl_addr a)
  | E.Union (s1,s2)       -> SL.Union (to_set s1, to_set s2)
  | E.Intr (s1,s2)        -> SL.Intr (to_set s1, to_set s2)
  | E.Setdiff (s1,s2)     -> SL.Setdiff (to_set s1, to_set s2)
  | E.PathToSet p         -> SL.PathToSet (path_to_tsl_path p)
  | E.AddrToSet _         -> raise(UnsupportedTslExpr(E.set_to_str s))
  | E.AddrToSetAt (m,a,l) -> SL.AddrToSet (mem_to_tsl_mem m,
                                               addr_to_tsl_addr a,
                                               int_to_tsl_int l)
  | E.SetArrayRd (E.VarArray v,t) ->
      SL.VarSet (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.SetArrayRd _        -> raise(UnsupportedTslExpr(E.set_to_str s))


and elem_to_tsl_elem (e:E.elem) : SL.elem =
(*  LOG "Entering elem_to_tsl_elem..." LEVEL TRACE; *)
(*  LOG "elem_to_tsl_elem(%s)" (E.elem_to_str e) LEVEL DEBUG; *)
  match e with
    E.VarElem v              -> SL.VarElem (var_to_tsl_var v)
  | E.CellData c             -> SL.CellData (cell_to_tsl_cell c)
  | E.ElemArrayRd (E.VarArray v,t) ->
      SL.VarElem (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.ElemArrayRd _          -> raise(UnsupportedTslExpr(E.elem_to_str e))
  | E.HavocListElem          -> raise(UnsupportedTslExpr(E.elem_to_str e))
  | E.HavocSkiplistElem      -> SL.HavocSkiplistElem
  | E.LowestElem             -> SL.LowestElem
  | E.HighestElem            -> SL.HighestElem


and addr_to_tsl_addr (a:E.addr) : SL.addr =
(*  LOG "Entering addr_to_tsl_addr..." LEVEL TRACE; *)
(*  LOG "addr_to_tsl_addr(%s)" (E.addr_to_str a) LEVEL DEBUG; *)
  match a with
    E.VarAddr v              -> SL.VarAddr (var_to_tsl_var v)
  | E.Null                   -> SL.Null
  | E.Next _                 -> raise(UnsupportedTslExpr(E.addr_to_str a))
  | E.NextAt _               -> raise(UnsupportedTslExpr(E.addr_to_str a))
  | E.ArrAt (c,l)            -> SL.ArrAt (cell_to_tsl_cell c, int_to_tsl_int l)
  | E.FirstLocked _          -> raise(UnsupportedTslExpr(E.addr_to_str a))
  | E.FirstLockedAt _        -> raise(UnsupportedTslExpr(E.addr_to_str a))
  | E.AddrArrayRd (E.VarArray v,t) ->
      SL.VarAddr (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.AddrArrayRd _          -> raise(UnsupportedTslExpr(E.addr_to_str a))
  | E.AddrArrRd (aa,i)       -> SL.AddrArrRd (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i)


and cell_to_tsl_cell (c:E.cell) : SL.cell =
(*  LOG "Entering cell_to_tsl_cell..." LEVEL TRACE; *)
(*  LOG "cell_to_tsl_cell(%s)" (E.cell_to_str c) LEVEL DEBUG; *)
  match c with
    E.VarCell v            -> SL.VarCell (var_to_tsl_var v)
  | E.Error                -> SL.Error
  | E.MkCell _             -> raise(UnsupportedTslExpr(E.cell_to_str c))
  | E.MkSLKCell _          -> raise(UnsupportedTslExpr(E.cell_to_str c))
  | E.MkSLCell (e,aa,tt,l) -> SL.MkCell (elem_to_tsl_elem e,
                                             addrarr_to_tsl_addrarr aa,
                                             tidarr_to_tsl_tidarr tt,
                                             int_to_tsl_int l)
  (* Tsl receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | E.CellLock _           -> raise(UnsupportedTslExpr(E.cell_to_str c))
  | E.CellLockAt (c,l,t)   -> SL.CellLockAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l,
                                                 tid_to_tsl_tid t)
  | E.CellUnlock _         -> raise(UnsupportedTslExpr(E.cell_to_str c))
  | E.CellUnlockAt (c,l)   -> SL.CellUnlockAt (cell_to_tsl_cell c,
                                                   int_to_tsl_int l)
  | E.CellAt (m,a)         -> SL.CellAt (mem_to_tsl_mem m, addr_to_tsl_addr a)
  | E.CellArrayRd (E.VarArray v,t) ->
      SL.VarCell (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.CellArrayRd _        -> raise(UnsupportedTslExpr(E.cell_to_str c))
  | E.UpdCellAddr _        -> raise(UnsupportedTslExpr(E.cell_to_str c))


and setth_to_tsl_setth (st:E.setth) : SL.setth =
(*  LOG "Entering setth_to_tsl_setth..." LEVEL TRACE; *)
(*  LOG "setth_to_tsl_setth(%s)" (E.setth_to_str st) LEVEL DEBUG; *)
  let to_setth = setth_to_tsl_setth in
  match st with
    E.VarSetTh v        -> SL.VarSetTh (var_to_tsl_var v)
  | E.EmptySetTh        -> SL.EmptySetTh
  | E.SinglTh t         -> SL.SinglTh (tid_to_tsl_tid t)
  | E.UnionTh (s1,s2)   -> SL.UnionTh (to_setth s1, to_setth s2)
  | E.IntrTh (s1,s2)    -> SL.IntrTh (to_setth s1, to_setth s2)
  | E.SetdiffTh (s1,s2) -> SL.SetdiffTh (to_setth s1, to_setth s2)
  | E.SetThArrayRd (E.VarArray v,t) ->
      SL.VarSetTh (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.SetThArrayRd _    -> raise(UnsupportedTslExpr(E.setth_to_str st))


and setelem_to_tsl_setelem (se:E.setelem) : SL.setelem =
(*  LOG "Entering setelem_to_tsl_setelem..." LEVEL TRACE; *)
(*  LOG "setelem_to_tsl_setelem(%s)" (E.setelem_to_str se) LEVEL DEBUG; *)
  let to_setelem = setelem_to_tsl_setelem in
  match se with
    E.VarSetElem v        -> SL.VarSetElem (var_to_tsl_var v)
  | E.EmptySetElem        -> SL.EmptySetElem
  | E.SinglElem e         -> SL.SinglElem (elem_to_tsl_elem e)
  | E.UnionElem (s1,s2)   -> SL.UnionElem (to_setelem s1, to_setelem s2)
  | E.IntrElem (s1,s2)    -> SL.IntrElem (to_setelem s1, to_setelem s2)
  | E.SetdiffElem (s1,s2) -> SL.SetdiffElem (to_setelem s1, to_setelem s2)
  | E.SetElemArrayRd (E.VarArray v,t) ->
      SL.VarSetElem (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.SetToElems (s,m)    -> SL.SetToElems (set_to_tsl_set s,
                                                mem_to_tsl_mem m)
  | E.SetElemArrayRd _    -> raise(UnsupportedTslExpr(E.setelem_to_str se))


and path_to_tsl_path (p:E.path) : SL.path =
(*  LOG "Entering path_to_tsl_path..." LEVEL TRACE; *)
(*  LOG "path_to_tsl_path(%s)" (E.path_to_str p) LEVEL DEBUG; *)
  match p with
    E.VarPath v             -> SL.VarPath (var_to_tsl_var v)
  | E.Epsilon               -> SL.Epsilon
  | E.SimplePath a          -> SL.SimplePath (addr_to_tsl_addr a)
  | E.GetPath _             -> raise(UnsupportedTslExpr(E.path_to_str p))
  | E.GetPathAt (m,a1,a2,l) -> SL.GetPath (mem_to_tsl_mem m,
                                               addr_to_tsl_addr a1,
                                               addr_to_tsl_addr a2,
                                               int_to_tsl_int l)
  | E.PathArrayRd _         -> raise(UnsupportedTslExpr(E.path_to_str p))


and mem_to_tsl_mem (m:E.mem) : SL.mem =
(*  LOG "Entering mem_to_tsl_mem..." LEVEL TRACE; *)
(*  LOG "mem_to_tsl_mem(%s)" (E.mem_to_str m) LEVEL DEBUG; *)
  match m with
    E.VarMem v       -> SL.VarMem (var_to_tsl_var v)
  | E.Update (m,a,c) -> SL.Update (mem_to_tsl_mem m,
                                       addr_to_tsl_addr a,
                                       cell_to_tsl_cell c)
  (* Missing the case for "emp" *)
  | E.MemArrayRd (E.VarArray v,t) ->
      SL.VarMem (var_to_tsl_var (E.var_set_param (E.Local t) v))
  | E.MemArrayRd _        -> raise(UnsupportedTslExpr(E.mem_to_str m))


and int_to_tsl_int (i:E.integer) : SL.integer =
(*  LOG "Entering int_to_tsl_int..." LEVEL TRACE; *)
(*  LOG "int_to_tsl_int(%s)" (E.integer_to_str i) LEVEL DEBUG; *)
  match i with
    E.IntVal i       -> SL.IntVal i
  | E.VarInt v       -> SL.VarInt (var_to_tsl_var v)
  | E.IntNeg i       -> SL.IntNeg (int_to_tsl_int i)
  | E.IntAdd (i1,i2) -> SL.IntAdd (int_to_tsl_int i1, int_to_tsl_int i2)
  | E.IntSub (i1,i2) -> SL.IntSub (int_to_tsl_int i1, int_to_tsl_int i2)
  | E.IntMul (i1,i2) -> SL.IntMul (int_to_tsl_int i1, int_to_tsl_int i2)
  | E.IntDiv (i1,i2) -> SL.IntDiv (int_to_tsl_int i1, int_to_tsl_int i2)
  | E.CellMax (c)    -> SL.CellMax (cell_to_tsl_cell c)
  | E.IntArrayRd _   -> raise(UnsupportedTslExpr(E.integer_to_str i))
  | E.IntSetMin _    -> raise(UnsupportedTslExpr(E.integer_to_str i))
  | E.IntSetMax _    -> raise(UnsupportedTslExpr(E.integer_to_str i))
  | E.HavocLevel     -> SL.HavocLevel


and addrarr_to_tsl_addrarr (arr:E.addrarr) : SL.addrarr =
(*  LOG "Entering addrarr_to_tsl_addrarr..." LEVEL TRACE; *)
(*  LOG "addrarr_to_tsl_addrarr(%s)" (E.addrarr_to_str arr) LEVEL DEBUG; *)
  match arr with
    E.VarAddrArray v       -> SL.VarAddrArray (var_to_tsl_var v)
  | E.AddrArrayUp (aa,i,a) -> SL.AddrArrayUp (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i,
                                                  addr_to_tsl_addr a)
  | E.CellArr c            -> SL.CellArr (cell_to_tsl_cell c)


and tidarr_to_tsl_tidarr (arr:E.tidarr) : SL.tidarr =
(*  LOG "Entering tidarr_to_tsl_tidarr..." LEVEL TRACE; *)
(*  LOG "tidarr_to_tsl_tidarr(%s)" (E.tidarr_to_str arr) LEVEL DEBUG; *)
  match arr with
    E.VarTidArray v       -> SL.VarTidArray (var_to_tsl_var v)
  | E.TidArrayUp (tt,i,t) -> SL.TidArrayUp (tidarr_to_tsl_tidarr tt,
                                                int_to_tsl_int i,
                                                tid_to_tsl_tid t)
  | E.CellTids c          -> SL.CellTids (cell_to_tsl_cell c)


and atom_to_tsl_atom (a:E.atom) : SL.atom =
(*  LOG "Entering atom_to_tsl_atom..." LEVEL TRACE; *)
(*  LOG "atom_to_tsl_atom(%s)" (E.atom_to_str a) LEVEL DEBUG; *)
  let path    = path_to_tsl_path       in
  let mem     = mem_to_tsl_mem         in
  let addr    = addr_to_tsl_addr       in
  let elem    = elem_to_tsl_elem       in
  let set     = set_to_tsl_set         in
  let tid     = tid_to_tsl_tid         in
  let setth   = setth_to_tsl_setth     in
  let setelem = setelem_to_tsl_setelem in
  let integ   = int_to_tsl_int         in
  let term    = term_to_tsl_term       in
  match a with
    E.Append (p1,p2,p3)        -> SL.Append (path p1,path p2,path p3)
  | E.Reach _                  -> raise(UnsupportedTslExpr(E.atom_to_str a))
  | E.ReachAt (m,a1,a2,l,p)    -> SL.Reach (mem m, addr a1, addr a2,
                                                integ l, path p)
  | E.OrderList(m,a1,a2)       -> SL.OrderList (mem m, addr a1, addr a2)
  | E.Skiplist(m,s,l,a1,a2,es) -> SL.Skiplist (mem m, set s, integ l,
                                                   addr a1, addr a2, setelem es)
  | E.In (a,s)                 -> SL.In (addr a, set s)
  | E.SubsetEq (s1,s2)         -> SL.SubsetEq (set s1, set s2)
  | E.InTh (t,s)               -> SL.InTh (tid t, setth s)
  | E.SubsetEqTh (s1,s2)       -> SL.SubsetEqTh (setth s1, setth s2)
  | E.InInt _                  -> raise(UnsupportedTslExpr(E.atom_to_str a))
  | E.SubsetEqInt _            -> raise(UnsupportedTslExpr(E.atom_to_str a))
  | E.InElem (e,s)             -> SL.InElem (elem_to_tsl_elem e, setelem s)
  | E.SubsetEqElem (s1,s2)     -> SL.SubsetEqElem (setelem s1, setelem s2)
  | E.Less (i1,i2)             -> SL.Less (integ i1, integ i2)
  | E.Greater (i1,i2)          -> SL.Greater (integ i1, integ i2)
  | E.LessEq (i1,i2)           -> SL.LessEq (integ i1, integ i2)
  | E.GreaterEq (i1,i2)        -> SL.GreaterEq (integ i1, integ i2)
  | E.LessTid _                -> raise(UnsupportedTslExpr(E.atom_to_str a))
  | E.LessElem (e1,e2)         -> SL.LessElem (elem e1, elem e2)
  | E.GreaterElem (e1,e2)      -> SL.GreaterElem (elem e1, elem e2)
  | E.Eq (t1,t2)               -> SL.Eq (term t1, term t2)
  | E.InEq (t1,t2)             -> SL.InEq (term t1, term t2)
  | E.BoolVar v                -> SL.BoolVar (var_to_tsl_var v)
  | E.BoolArrayRd _            -> raise(UnsupportedTslExpr(E.atom_to_str a))
  | E.PC (pc,t,pr)             -> SL.PC (pc, shared_to_tsl_shared t,pr)
  | E.PCUpdate (pc,t)          -> SL.PCUpdate (pc, tid_to_tsl_tid t)
  | E.PCRange (pc1,pc2,t,pr)   -> SL.PCRange (pc1, pc2, shared_to_tsl_shared t, pr)


and literal_to_tsl_literal (l:E.literal) : SL.literal =
(*  LOG "Entering literal_to_tsl_literal..." LEVEL TRACE; *)
(*  LOG "literal_to_tsl_literal(%s)" (E.literal_to_str l) LEVEL DEBUG; *)
  match l with
    E.Atom a    -> SL.Atom (atom_to_tsl_atom a)
  | E.NegAtom a -> SL.NegAtom (atom_to_tsl_atom a)


and formula_to_tsl_formula (f:E.formula) : SL.formula =
(*  LOG "Entering formula_to_tsl_formula..." LEVEL TRACE; *)
(*  LOG "formula_to_tsl_formula(%s)" (E.formula_to_str f) LEVEL DEBUG; *)
  let to_formula = formula_to_tsl_formula in
  match f with
    E.Literal l       -> SL.Literal (literal_to_tsl_literal l)
  | E.True            -> SL.True
  | E.False           -> SL.False
  | E.And (f1,f2)     -> SL.And (to_formula f1, to_formula f2)
  | E.Or (f1,f2)      -> SL.Or (to_formula f1, to_formula f2)
  | E.Not f1          -> SL.Not (to_formula f1)
  | E.Implies (f1,f2) -> SL.Implies (to_formula f1, to_formula f2)
  | E.Iff (f1,f2)     -> SL.Iff (to_formula f1, to_formula f2)




(* TslExpression to Expression conversion *)


let rec tsl_sort_to_sort (s:SL.sort) : E.sort =
  match s with
  | SL.Set       -> E.Set
  | SL.Elem      -> E.Elem
  | SL.Tid      -> E.Tid
  | SL.Addr      -> E.Addr
  | SL.Cell      -> E.Cell
  | SL.SetTh     -> E.SetTh
  | SL.SetElem   -> E.SetElem
  | SL.Path      -> E.Path
  | SL.Mem       -> E.Mem
  | SL.Int       -> E.Int
  | SL.AddrArray -> E.AddrArray
  | SL.TidArray  -> E.TidArray
  | SL.Bool      -> E.Bool
  | SL.Unknown   -> E.Unknown


and var_to_expr_var (v:SL.variable) : E.variable =
  E.build_var (SL.var_id v)
              (tsl_sort_to_sort (SL.var_sort v))
              (SL.var_is_primed v)
              (shared_to_expr_shared (SL.var_parameter v))
              (scope_to_expr_scope (SL.var_scope v))
              (E.RealVar)


and shared_to_expr_shared (th:SL.shared_or_local) : E.shared_or_local =
  match th with
  | SL.Shared  -> E.Shared
  | SL.Local t -> E.Local (tid_to_expr_tid t)


and scope_to_expr_scope (p:SL.procedure_name) : E.procedure_name =
  match p with
  | SL.GlobalScope -> E.GlobalScope
  | SL.Scope proc  -> E.Scope proc


and tid_to_expr_tid (th:SL.tid) : E.tid =
  match th with
  | SL.VarTh v            -> E.VarTh (var_to_expr_var v)
  | SL.NoTid             -> E.NoTid
  | SL.CellLockIdAt (c,l) -> E.CellLockIdAt (cell_to_expr_cell c,
                                                 int_to_expr_int l)
  | SL.TidArrRd (tt,i)   -> E.TidArrRd (tidarr_to_expr_tidarr tt,
                                              int_to_expr_int i)


and term_to_expr_term (t:SL.term) : E.term =
  match t with
  | SL.VarT v        -> E.VarT (var_to_expr_var v)
  | SL.SetT s        -> E.SetT (set_to_expr_set s)
  | SL.ElemT e       -> E.ElemT (elem_to_expr_elem e)
  | SL.TidT t       -> E.TidT (tid_to_expr_tid t)
  | SL.AddrT a       -> E.AddrT (addr_to_expr_addr a)
  | SL.CellT c       -> E.CellT (cell_to_expr_cell c)
  | SL.SetThT st     -> E.SetThT (setth_to_expr_setth st)
  | SL.SetElemT st   -> E.SetElemT (setelem_to_expr_setelem st)
  | SL.PathT p       -> E.PathT (path_to_expr_path p)
  | SL.MemT m        -> E.MemT (mem_to_expr_mem m)
  | SL.IntT i        -> E.IntT (int_to_expr_int i)
  | SL.AddrArrayT aa -> E.AddrArrayT (addrarr_to_expr_addrarr aa)
  | SL.TidArrayT tt  -> E.TidArrayT (tidarr_to_expr_tidarr tt)
  | SL.VarUpdate (v,th,t) ->
      let expr_a  = E.VarArray (var_to_expr_var v) in
      let expr_th = tid_to_expr_tid th in
      let expr_t  = E.Term (term_to_expr_term t)
      in
        E.ArrayT (E.ArrayUp (expr_a, expr_th, expr_t))



and eq_to_expr_eq ((t1,t2):SL.eq) : E.eq =
  (term_to_expr_term t1, term_to_expr_term t2)


and diseq_to_expr_diseq ((t1,t2):SL.diseq) : E.diseq =
  (term_to_expr_term t1, term_to_expr_term t2)


and set_to_expr_set (s:SL.set) : E.set =
  let to_set = set_to_expr_set in
  match s with
  | SL.VarSet v            -> E.VarSet (var_to_expr_var v)
  | SL.EmptySet            -> E.EmptySet
  | SL.Singl a             -> E.Singl (addr_to_expr_addr a)
  | SL.Union (s1,s2)       -> E.Union (to_set s1, to_set s2)
  | SL.Intr (s1,s2)        -> E.Intr (to_set s1, to_set s2)
  | SL.Setdiff (s1,s2)     -> E.Setdiff (to_set s1, to_set s2)
  | SL.PathToSet p         -> E.PathToSet (path_to_expr_path p)
  | SL.AddrToSet (m,a,l)   -> E.AddrToSetAt (mem_to_expr_mem m,
                                                 addr_to_expr_addr a,
                                                 int_to_expr_int l)


and elem_to_expr_elem (e:SL.elem) : E.elem =
  match e with
  | SL.VarElem v              -> E.VarElem (var_to_expr_var v)
  | SL.CellData c             -> E.CellData (cell_to_expr_cell c)
  | SL.HavocSkiplistElem      -> E.HavocSkiplistElem
  | SL.LowestElem             -> E.LowestElem
  | SL.HighestElem            -> E.HighestElem


and addr_to_expr_addr (a:SL.addr) : E.addr =
  match a with
  | SL.VarAddr v              -> E.VarAddr (var_to_expr_var v)
  | SL.Null                   -> E.Null
  | SL.ArrAt (c,l)           -> E.ArrAt (cell_to_expr_cell c, int_to_expr_int l)
  | SL.AddrArrRd (aa,i)       -> E.AddrArrRd (addrarr_to_expr_addrarr aa,
                                                  int_to_expr_int i)


and cell_to_expr_cell (c:SL.cell) : E.cell =
  match c with
    SL.VarCell v          -> E.VarCell (var_to_expr_var v)
  | SL.Error              -> E.Error
  | SL.MkCell (e,aa,tt,l) -> E.MkSLCell (elem_to_expr_elem e,
                                             addrarr_to_expr_addrarr aa,
                                             tidarr_to_expr_tidarr tt,
                                             int_to_expr_int l)
  | SL.CellLockAt (c,l, t)-> E.CellLockAt (cell_to_expr_cell c,
                                               int_to_expr_int l,
                                               tid_to_expr_tid t)
  | SL.CellUnlockAt (c,l) -> E.CellUnlockAt (cell_to_expr_cell c,
                                                 int_to_expr_int l)
  | SL.CellAt (m,a)       -> E.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


and setth_to_expr_setth (st:SL.setth) : E.setth =
  let to_setth = setth_to_expr_setth in
  match st with
  | SL.VarSetTh v        -> E.VarSetTh (var_to_expr_var v)
  | SL.EmptySetTh        -> E.EmptySetTh
  | SL.SinglTh t         -> E.SinglTh (tid_to_expr_tid t)
  | SL.UnionTh (s1,s2)   -> E.UnionTh (to_setth s1, to_setth s2)
  | SL.IntrTh (s1,s2)    -> E.IntrTh (to_setth s1, to_setth s2)
  | SL.SetdiffTh (s1,s2) -> E.SetdiffTh (to_setth s1, to_setth s2)


and setelem_to_expr_setelem (st:SL.setelem) : E.setelem =
  let to_setelem = setelem_to_expr_setelem in
  match st with
  | SL.VarSetElem v        -> E.VarSetElem (var_to_expr_var v)
  | SL.EmptySetElem        -> E.EmptySetElem
  | SL.SinglElem e         -> E.SinglElem (elem_to_expr_elem e)
  | SL.UnionElem (s1,s2)   -> E.UnionElem (to_setelem s1, to_setelem s2)
  | SL.IntrElem (s1,s2)    -> E.IntrElem (to_setelem s1, to_setelem s2)
  | SL.SetdiffElem (s1,s2) -> E.SetdiffElem (to_setelem s1, to_setelem s2)
  | SL.SetToElems (s,m)    -> E.SetToElems (set_to_expr_set s,
                                                mem_to_expr_mem m)


and path_to_expr_path (p:SL.path) : E.path =
  match p with
  | SL.VarPath v             -> E.VarPath (var_to_expr_var v)
  | SL.Epsilon               -> E.Epsilon
  | SL.SimplePath a          -> E.SimplePath (addr_to_expr_addr a)
  | SL.GetPath (m,a1,a2,l)   -> E.GetPathAt (mem_to_expr_mem m,
                                                 addr_to_expr_addr a1,
                                                 addr_to_expr_addr a2,
                                                 int_to_expr_int l)


and mem_to_expr_mem (m:SL.mem) : E.mem =
  match m with
  | SL.VarMem v       -> E.VarMem (var_to_expr_var v)
  | SL.Update (m,a,c) -> E.Update (mem_to_expr_mem m,
                                       addr_to_expr_addr a,
                                       cell_to_expr_cell c)


and int_to_expr_int (i:SL.integer) : E.integer =
  match i with
  | SL.IntVal i       -> E.IntVal i
  | SL.VarInt v       -> E.VarInt (var_to_expr_var v)
  | SL.IntNeg i       -> E.IntNeg (int_to_expr_int i)
  | SL.IntAdd (i1,i2) -> E.IntAdd (int_to_expr_int i1, int_to_expr_int i2)
  | SL.IntSub (i1,i2) -> E.IntSub (int_to_expr_int i1, int_to_expr_int i2)
  | SL.IntMul (i1,i2) -> E.IntMul (int_to_expr_int i1, int_to_expr_int i2)
  | SL.IntDiv (i1,i2) -> E.IntDiv (int_to_expr_int i1, int_to_expr_int i2)
  | SL.CellMax (c)    -> E.CellMax (cell_to_expr_cell c)
  | SL.HavocLevel     -> E.HavocLevel


and addrarr_to_expr_addrarr (arr:SL.addrarr) : E.addrarr =
  match arr with
  | SL.VarAddrArray v       -> E.VarAddrArray (var_to_expr_var v)
  | SL.AddrArrayUp (aa,i,a) -> E.AddrArrayUp (addrarr_to_expr_addrarr aa,
                                                  int_to_expr_int i,
                                                  addr_to_expr_addr a)
  | SL.CellArr c            -> E.CellArr (cell_to_expr_cell c)


and tidarr_to_expr_tidarr (arr:SL.tidarr) : E.tidarr =
  match arr with
  | SL.VarTidArray v       -> E.VarTidArray (var_to_expr_var v)
  | SL.TidArrayUp (tt,i,t) -> E.TidArrayUp (tidarr_to_expr_tidarr tt,
                                                int_to_expr_int i,
                                                tid_to_expr_tid t)
  | SL.CellTids c          -> E.CellTids (cell_to_expr_cell c)


and tsl_atom_to_atom (a:SL.atom) : E.atom =
  let path    = path_to_expr_path       in
  let mem     = mem_to_expr_mem         in
  let addr    = addr_to_expr_addr       in
  let elem    = elem_to_expr_elem       in
  let set     = set_to_expr_set         in
  let tid     = tid_to_expr_tid         in
  let setth   = setth_to_expr_setth     in
  let setelem = setelem_to_expr_setelem in
  let integ   = int_to_expr_int         in
  let term    = term_to_expr_term       in
  match a with
    SL.Append (p1,p2,p3)        -> E.Append (path p1,path p2,path p3)
  | SL.Reach (m,a1,a2,l,p  )    -> E.ReachAt (mem m, addr a1, addr a2,
                                                integ l, path p)
  | SL.OrderList(m,a1,a2)       -> E.OrderList (mem m, addr a1, addr a2)
  | SL.Skiplist(m,s,l,a1,a2,es) -> E.Skiplist (mem m, set s, integ l,
                                                   addr a1, addr a2, setelem es)
  | SL.In (a,s)                 -> E.In (addr a, set s)
  | SL.SubsetEq (s1,s2)         -> E.SubsetEq (set s1, set s2)
  | SL.InTh (t,s)               -> E.InTh (tid t, setth s)
  | SL.SubsetEqTh (s1,s2)       -> E.SubsetEqTh (setth s1, setth s2)
  | SL.InElem (e,s)             -> E.InElem (elem_to_expr_elem e, setelem s)
  | SL.SubsetEqElem (s1,s2)     -> E.SubsetEqElem (setelem s1, setelem s2)
  | SL.Less (i1,i2)             -> E.Less (integ i1, integ i2)
  | SL.Greater (i1,i2)          -> E.Greater (integ i1, integ i2)
  | SL.LessEq (i1,i2)           -> E.LessEq (integ i1, integ i2)
  | SL.GreaterEq (i1,i2)        -> E.GreaterEq (integ i1, integ i2)
  | SL.LessElem (e1,e2)         -> E.LessElem (elem e1, elem e2)
  | SL.GreaterElem (e1,e2)      -> E.GreaterElem (elem e1, elem e2)
  | SL.Eq (t1,t2)               -> E.Eq (term t1, term t2)
  | SL.InEq (t1,t2)             -> E.InEq (term t1, term t2)
  | SL.BoolVar v                -> E.BoolVar (var_to_expr_var v)
  | SL.PC (pc,t,pr)             -> E.PC (pc, shared_to_expr_shared t,pr)
  | SL.PCUpdate (pc,t)          -> E.PCUpdate (pc, tid_to_expr_tid t)
  | SL.PCRange (pc1,pc2,t,pr)   -> E.PCRange (pc1, pc2,shared_to_expr_shared t,pr)


and literal_to_expr_literal (l:SL.literal) : E.literal =
  match l with
    SL.Atom a    -> E.Atom (tsl_atom_to_atom a)
  | SL.NegAtom a -> E.NegAtom (tsl_atom_to_atom a)


and formula_to_expr_formula (f:SL.formula) : E.formula =
  let to_formula = formula_to_expr_formula in
  match f with
    SL.Literal l       -> E.Literal (literal_to_expr_literal l)
  | SL.True            -> E.True
  | SL.False           -> E.False
  | SL.And (f1,f2)     -> E.And (to_formula f1, to_formula f2)
  | SL.Or (f1,f2)      -> E.Or (to_formula f1, to_formula f2)
  | SL.Not f1          -> E.Not (to_formula f1)
  | SL.Implies (f1,f2) -> E.Implies (to_formula f1, to_formula f2)
  | SL.Iff (f1,f2)     -> E.Iff (to_formula f1, to_formula f2)
