open LeapLib

module Expr=Expression
module Tsl=TSLExpression


type varId = Expr.varId
type sort  = Expr.sort
type tid   = Expr.tid

exception UnsupportedSort of string
exception UnsupportedTslExpr of string



(* Expression to TslExpression conversion *)


let rec sort_to_tsl_sort (s:Expr.sort) : Tsl.sort =
(*  LOG "Entering sort_to_tsl_sort..." LEVEL TRACE; *)
(*  LOG "sort_to_tsl_sort(%s)" (Expr.sort_to_str s) LEVEL DEBUG; *)
  match s with
    Expr.Set       -> Tsl.Set
  | Expr.Elem      -> Tsl.Elem
  | Expr.Thid      -> Tsl.Thid
  | Expr.Addr      -> Tsl.Addr
  | Expr.Cell      -> Tsl.Cell
  | Expr.SetTh     -> Tsl.SetTh
  | Expr.SetInt    -> raise(UnsupportedSort(Expr.sort_to_str s))
  | Expr.SetElem   -> Tsl.SetElem
  | Expr.Path      -> Tsl.Path
  | Expr.Mem       -> Tsl.Mem
  | Expr.Bool      -> Tsl.Bool
  | Expr.Int       -> Tsl.Int
  | Expr.Array     -> raise(UnsupportedSort(Expr.sort_to_str s))
  | Expr.AddrArray -> Tsl.AddrArray
  | Expr.TidArray  -> Tsl.TidArray
  | Expr.Unknown   -> Tsl.Unknown



and build_term_var (v:Expr.variable) : Tsl.term =
(*  LOG "Entering build_term_var..." LEVEL TRACE; *)
(*  LOG "build_term_var(%s)" (Expr.variable_to_str v) LEVEL DEBUG; *)
  let tsl_v = var_to_tsl_var v in
  match Expr.var_sort v with
    Expr.Set       -> Tsl.SetT       (Tsl.VarSet        tsl_v)
  | Expr.Elem      -> Tsl.ElemT      (Tsl.VarElem       tsl_v)
  | Expr.Thid      -> Tsl.ThidT      (Tsl.VarTh         tsl_v)
  | Expr.Addr      -> Tsl.AddrT      (Tsl.VarAddr       tsl_v)
  | Expr.Cell      -> Tsl.CellT      (Tsl.VarCell       tsl_v)
  | Expr.SetTh     -> Tsl.SetThT     (Tsl.VarSetTh      tsl_v)
  | Expr.Path      -> Tsl.PathT      (Tsl.VarPath       tsl_v)
  | Expr.Mem       -> Tsl.MemT       (Tsl.VarMem        tsl_v)
  | Expr.Int       -> Tsl.IntT       (Tsl.VarInt        tsl_v)
  | Expr.AddrArray -> Tsl.AddrArrayT (Tsl.VarAddrArray  tsl_v)
  | Expr.TidArray  -> Tsl.TidArrayT  (Tsl.VarTidArray   tsl_v)
  | _              -> Tsl.VarT       (tsl_v)



and var_to_tsl_var (v:Expr.variable) : Tsl.variable =
(*  LOG "Entering var_to_tsl_var..." LEVEL TRACE; *)
(*  LOG "var_to_tsl_var(%s)" (Expr.variable_to_str v) LEVEL DEBUG; *)
  let (id,s,pr,th,p,_) = v
  in
    (id, sort_to_tsl_sort s, pr, Option.lift tid_to_tsl_tid th, p)



and tid_to_tsl_tid (th:Expr.tid) : Tsl.tid =
(*  LOG "Entering tid_to_tsl_tid..." LEVEL TRACE; *)
(*  LOG "tid_to_tsl_tid(%s)" (Expr.tid_to_str th) LEVEL DEBUG; *)
  match th with
    Expr.VarTh v            -> Tsl.VarTh (var_to_tsl_var v)
  | Expr.NoThid             -> Tsl.NoThid
  | Expr.CellLockId _       -> raise(UnsupportedTslExpr(Expr.tid_to_str th))
  | Expr.CellLockIdAt (c,l) -> Tsl.CellLockIdAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l)
  | Expr.ThidArrayRd _      -> raise(UnsupportedTslExpr(Expr.tid_to_str th))
  | Expr.ThidArrRd (tt,i)   -> Tsl.ThidArrRd (tidarr_to_tsl_tidarr tt,
                                              int_to_tsl_int i)

and term_to_tsl_term (t:Expr.term) : Tsl.term =
(*  LOG "Entering term_to_tsl_term..." LEVEL TRACE; *)
(*  LOG "term_to_tsl_term(%s)" (Expr.term_to_str t) LEVEL DEBUG; *)
  match t with
    Expr.VarT v        -> Tsl.VarT (var_to_tsl_var v)
  | Expr.SetT s        -> Tsl.SetT (set_to_tsl_set s)
  | Expr.ElemT e       -> Tsl.ElemT (elem_to_tsl_elem e)
  | Expr.ThidT t       -> Tsl.ThidT (tid_to_tsl_tid t)
  | Expr.AddrT a       -> Tsl.AddrT (addr_to_tsl_addr a)
  | Expr.CellT c       -> Tsl.CellT (cell_to_tsl_cell c)
  | Expr.SetThT st     -> Tsl.SetThT (setth_to_tsl_setth st)
  | Expr.SetIntT _     -> raise(UnsupportedTslExpr(Expr.term_to_str t))
  | Expr.SetElemT st   -> Tsl.SetElemT (setelem_to_tsl_setelem st)
  | Expr.PathT p       -> Tsl.PathT (path_to_tsl_path p)
  | Expr.MemT m        -> Tsl.MemT (mem_to_tsl_mem m)
  | Expr.IntT i        -> Tsl.IntT (int_to_tsl_int i)
  | Expr.AddrArrayT aa -> Tsl.AddrArrayT (addrarr_to_tsl_addrarr aa)
  | Expr.TidArrayT tt  -> Tsl.TidArrayT (tidarr_to_tsl_tidarr tt)
  | Expr.ArrayT a      -> arrays_to_tsl_term a


and arrays_to_tsl_term (a:Expr.arrays) : Tsl.term =
  match a with
  | Expr.VarArray v -> build_term_var v
  | Expr.ArrayUp (Expr.VarArray v,th_p,Expr.Term t) ->
      let tsl_v  = var_to_tsl_var v in
      let tsl_th = tid_to_tsl_tid th_p in
      let tsl_t  = term_to_tsl_term t
      in
        Tsl.VarUpdate (tsl_v, tsl_th, tsl_t)
  | Expr.ArrayUp (_,_,e) -> raise(UnsupportedTslExpr(Expr.expr_to_str e))


and eq_to_tsl_eq ((t1,t2):Expr.eq) : Tsl.eq =
(*  LOG "Entering eq_to_tsl_eq..." LEVEL TRACE; *)
(*  LOG "eq_to_tsl_eq(%s,%s)" (Expr.term_to_str t1) *)
(*                            (Expr.term_to_str t2) LEVEL DEBUG; *)
  (term_to_tsl_term t1, term_to_tsl_term t2)


and diseq_to_tsl_diseq ((t1,t2):Expr.diseq) : Tsl.diseq =
(*  LOG "Entering diseq_to_tsl_diseq..." LEVEL TRACE; *)
(*  LOG "diseq_to_tsl_diseq(%s,%s)" (Expr.term_to_str t1) *)
(*                                  (Expr.term_to_str t2) LEVEL DEBUG; *)
  (term_to_tsl_term t1, term_to_tsl_term t2)


and set_to_tsl_set (s:Expr.set) : Tsl.set =
(*  LOG "Entering set_to_tsl_set..." LEVEL TRACE; *)
(*  LOG "set_to_tsl_set(%s)" (Expr.set_to_str s) LEVEL DEBUG; *)
  let to_set = set_to_tsl_set in
  match s with
    Expr.VarSet v            -> Tsl.VarSet (var_to_tsl_var v)
  | Expr.EmptySet            -> Tsl.EmptySet
  | Expr.Singl a             -> Tsl.Singl (addr_to_tsl_addr a)
  | Expr.Union (s1,s2)       -> Tsl.Union (to_set s1, to_set s2)
  | Expr.Intr (s1,s2)        -> Tsl.Intr (to_set s1, to_set s2)
  | Expr.Setdiff (s1,s2)     -> Tsl.Setdiff (to_set s1, to_set s2)
  | Expr.PathToSet p         -> Tsl.PathToSet (path_to_tsl_path p)
  | Expr.AddrToSet _         -> raise(UnsupportedTslExpr(Expr.set_to_str s))
  | Expr.AddrToSetAt (m,a,l) -> Tsl.AddrToSet (mem_to_tsl_mem m,
                                               addr_to_tsl_addr a,
                                               int_to_tsl_int l)
  | Expr.SetArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarSet (var_to_tsl_var v)
  | Expr.SetArrayRd _        -> raise(UnsupportedTslExpr(Expr.set_to_str s))


and elem_to_tsl_elem (e:Expr.elem) : Tsl.elem =
(*  LOG "Entering elem_to_tsl_elem..." LEVEL TRACE; *)
(*  LOG "elem_to_tsl_elem(%s)" (Expr.elem_to_str e) LEVEL DEBUG; *)
  match e with
    Expr.VarElem v              -> Tsl.VarElem (var_to_tsl_var v)
  | Expr.CellData c             -> Tsl.CellData (cell_to_tsl_cell c)
  | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarElem (var_to_tsl_var v)
  | Expr.ElemArrayRd _          -> raise(UnsupportedTslExpr(Expr.elem_to_str e))
  | Expr.HavocListElem          -> raise(UnsupportedTslExpr(Expr.elem_to_str e))
  | Expr.HavocSkiplistElem      -> Tsl.HavocSkiplistElem
  | Expr.LowestElem             -> Tsl.LowestElem
  | Expr.HighestElem            -> Tsl.HighestElem


and addr_to_tsl_addr (a:Expr.addr) : Tsl.addr =
(*  LOG "Entering addr_to_tsl_addr..." LEVEL TRACE; *)
(*  LOG "addr_to_tsl_addr(%s)" (Expr.addr_to_str a) LEVEL DEBUG; *)
  match a with
    Expr.VarAddr v              -> Tsl.VarAddr (var_to_tsl_var v)
  | Expr.Null                   -> Tsl.Null
  | Expr.Next _                 -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.NextAt (c,l)           -> Tsl.NextAt (cell_to_tsl_cell c, int_to_tsl_int l)
  | Expr.FirstLocked _          -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.FirstLockedAt _        -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarAddr (var_to_tsl_var v)
  | Expr.AddrArrayRd _          -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.AddrArrRd (aa,i)       -> Tsl.AddrArrRd (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i)


and cell_to_tsl_cell (c:Expr.cell) : Tsl.cell =
(*  LOG "Entering cell_to_tsl_cell..." LEVEL TRACE; *)
(*  LOG "cell_to_tsl_cell(%s)" (Expr.cell_to_str c) LEVEL DEBUG; *)
  match c with
    Expr.VarCell v            -> Tsl.VarCell (var_to_tsl_var v)
  | Expr.Error                -> Tsl.Error
  | Expr.MkCell _             -> raise(UnsupportedTslExpr(Expr.cell_to_str c))
  | Expr.MkSLKCell _          -> raise(UnsupportedTslExpr(Expr.cell_to_str c))
  | Expr.MkSLCell (e,aa,tt,l) -> Tsl.MkCell (elem_to_tsl_elem e,
                                             addrarr_to_tsl_addrarr aa,
                                             tidarr_to_tsl_tidarr tt,
                                             int_to_tsl_int l)
  (* Tsl receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | Expr.CellLock _           -> raise(UnsupportedTslExpr(Expr.cell_to_str c))
  | Expr.CellLockAt (c,l,t)   -> Tsl.CellLockAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l,
                                                 tid_to_tsl_tid t)
  | Expr.CellUnlock _         -> raise(UnsupportedTslExpr(Expr.cell_to_str c))
  | Expr.CellUnlockAt (c,l)   -> Tsl.CellUnlockAt (cell_to_tsl_cell c,
                                                   int_to_tsl_int l)
  | Expr.CellAt (m,a)         -> Tsl.CellAt (mem_to_tsl_mem m, addr_to_tsl_addr a)
  | Expr.CellArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarCell (var_to_tsl_var v)
  | Expr.CellArrayRd _        -> raise(UnsupportedTslExpr(Expr.cell_to_str c))


and setth_to_tsl_setth (st:Expr.setth) : Tsl.setth =
(*  LOG "Entering setth_to_tsl_setth..." LEVEL TRACE; *)
(*  LOG "setth_to_tsl_setth(%s)" (Expr.setth_to_str st) LEVEL DEBUG; *)
  let to_setth = setth_to_tsl_setth in
  match st with
    Expr.VarSetTh v        -> Tsl.VarSetTh (var_to_tsl_var v)
  | Expr.EmptySetTh        -> Tsl.EmptySetTh
  | Expr.SinglTh t         -> Tsl.SinglTh (tid_to_tsl_tid t)
  | Expr.UnionTh (s1,s2)   -> Tsl.UnionTh (to_setth s1, to_setth s2)
  | Expr.IntrTh (s1,s2)    -> Tsl.IntrTh (to_setth s1, to_setth s2)
  | Expr.SetdiffTh (s1,s2) -> Tsl.SetdiffTh (to_setth s1, to_setth s2)
  | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarSetTh (var_to_tsl_var v)
  | Expr.SetThArrayRd _    -> raise(UnsupportedTslExpr(Expr.setth_to_str st))


and setelem_to_tsl_setelem (se:Expr.setelem) : Tsl.setelem =
(*  LOG "Entering setelem_to_tsl_setelem..." LEVEL TRACE; *)
(*  LOG "setelem_to_tsl_setelem(%s)" (Expr.setelem_to_str se) LEVEL DEBUG; *)
  let to_setelem = setelem_to_tsl_setelem in
  match se with
    Expr.VarSetElem v        -> Tsl.VarSetElem (var_to_tsl_var v)
  | Expr.EmptySetElem        -> Tsl.EmptySetElem
  | Expr.SinglElem e         -> Tsl.SinglElem (elem_to_tsl_elem e)
  | Expr.UnionElem (s1,s2)   -> Tsl.UnionElem (to_setelem s1, to_setelem s2)
  | Expr.IntrElem (s1,s2)    -> Tsl.IntrElem (to_setelem s1, to_setelem s2)
  | Expr.SetdiffElem (s1,s2) -> Tsl.SetdiffElem (to_setelem s1, to_setelem s2)
  | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarSetElem (var_to_tsl_var v)
  | Expr.SetToElems (s,m)    -> Tsl.SetToElems (set_to_tsl_set s,
                                                mem_to_tsl_mem m)
  | Expr.SetElemArrayRd _    -> raise(UnsupportedTslExpr(Expr.setelem_to_str se))


and path_to_tsl_path (p:Expr.path) : Tsl.path =
(*  LOG "Entering path_to_tsl_path..." LEVEL TRACE; *)
(*  LOG "path_to_tsl_path(%s)" (Expr.path_to_str p) LEVEL DEBUG; *)
  match p with
    Expr.VarPath v             -> Tsl.VarPath (var_to_tsl_var v)
  | Expr.Epsilon               -> Tsl.Epsilon
  | Expr.SimplePath a          -> Tsl.SimplePath (addr_to_tsl_addr a)
  | Expr.GetPath _             -> raise(UnsupportedTslExpr(Expr.path_to_str p))
  | Expr.GetPathAt (m,a1,a2,l) -> Tsl.GetPath (mem_to_tsl_mem m,
                                               addr_to_tsl_addr a1,
                                               addr_to_tsl_addr a2,
                                               int_to_tsl_int l)
  | Expr.PathArrayRd _         -> raise(UnsupportedTslExpr(Expr.path_to_str p))


and mem_to_tsl_mem (m:Expr.mem) : Tsl.mem =
(*  LOG "Entering mem_to_tsl_mem..." LEVEL TRACE; *)
(*  LOG "mem_to_tsl_mem(%s)" (Expr.mem_to_str m) LEVEL DEBUG; *)
  match m with
    Expr.VarMem v       -> Tsl.VarMem (var_to_tsl_var v)
  | Expr.Update (m,a,c) -> Tsl.Update (mem_to_tsl_mem m,
                                       addr_to_tsl_addr a,
                                       cell_to_tsl_cell c)
  (* Missing the case for "emp" *)
  | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarMem (var_to_tsl_var v)
  | Expr.MemArrayRd _        -> raise(UnsupportedTslExpr(Expr.mem_to_str m))


and int_to_tsl_int (i:Expr.integer) : Tsl.integer =
(*  LOG "Entering int_to_tsl_int..." LEVEL TRACE; *)
(*  LOG "int_to_tsl_int(%s)" (Expr.integer_to_str i) LEVEL DEBUG; *)
  match i with
    Expr.IntVal i       -> Tsl.IntVal i
  | Expr.VarInt v       -> Tsl.VarInt (var_to_tsl_var v)
  | Expr.IntNeg i       -> Tsl.IntNeg (int_to_tsl_int i)
  | Expr.IntAdd (i1,i2) -> Tsl.IntAdd (int_to_tsl_int i1, int_to_tsl_int i2)
  | Expr.IntSub (i1,i2) -> Tsl.IntSub (int_to_tsl_int i1, int_to_tsl_int i2)
  | Expr.IntMul (i1,i2) -> Tsl.IntMul (int_to_tsl_int i1, int_to_tsl_int i2)
  | Expr.IntDiv (i1,i2) -> Tsl.IntDiv (int_to_tsl_int i1, int_to_tsl_int i2)
  | Expr.CellMax (c)    -> Tsl.CellMax (cell_to_tsl_cell c)
  | Expr.IntArrayRd _   -> raise(UnsupportedTslExpr(Expr.integer_to_str i))
  | Expr.IntSetMin _    -> raise(UnsupportedTslExpr(Expr.integer_to_str i))
  | Expr.IntSetMax _    -> raise(UnsupportedTslExpr(Expr.integer_to_str i))
  | Expr.HavocLevel     -> Tsl.HavocLevel


and addrarr_to_tsl_addrarr (arr:Expr.addrarr) : Tsl.addrarr =
(*  LOG "Entering addrarr_to_tsl_addrarr..." LEVEL TRACE; *)
(*  LOG "addrarr_to_tsl_addrarr(%s)" (Expr.addrarr_to_str arr) LEVEL DEBUG; *)
  match arr with
    Expr.VarAddrArray v       -> Tsl.VarAddrArray (var_to_tsl_var v)
  | Expr.AddrArrayUp (aa,i,a) -> Tsl.AddrArrayUp (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i,
                                                  addr_to_tsl_addr a)
  | Expr.CellArr c            -> Tsl.CellArr (cell_to_tsl_cell c)


and tidarr_to_tsl_tidarr (arr:Expr.tidarr) : Tsl.tidarr =
(*  LOG "Entering tidarr_to_tsl_tidarr..." LEVEL TRACE; *)
(*  LOG "tidarr_to_tsl_tidarr(%s)" (Expr.tidarr_to_str arr) LEVEL DEBUG; *)
  match arr with
    Expr.VarTidArray v       -> Tsl.VarTidArray (var_to_tsl_var v)
  | Expr.TidArrayUp (tt,i,t) -> Tsl.TidArrayUp (tidarr_to_tsl_tidarr tt,
                                                int_to_tsl_int i,
                                                tid_to_tsl_tid t)
  | Expr.CellTids c          -> Tsl.CellTids (cell_to_tsl_cell c)


and atom_to_tsl_atom (a:Expr.atom) : Tsl.atom =
(*  LOG "Entering atom_to_tsl_atom..." LEVEL TRACE; *)
(*  LOG "atom_to_tsl_atom(%s)" (Expr.atom_to_str a) LEVEL DEBUG; *)
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
    Expr.Append (p1,p2,p3)    -> Tsl.Append (path p1,path p2,path p3)
  | Expr.Reach _              -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.ReachAt (m,a1,a2,l,p)-> Tsl.Reach (mem m, addr a1, addr a2,
                                            integ l, path p)
  | Expr.OrderList(m,a1,a2)   -> Tsl.OrderList (mem m, addr a1, addr a2)
  | Expr.Skiplist(m,s,l,a1,a2)-> Tsl.Skiplist (mem m, set s, integ l,
                                               addr a1, addr a2)
  | Expr.In (a,s)             -> Tsl.In (addr a, set s)
  | Expr.SubsetEq (s1,s2)     -> Tsl.SubsetEq (set s1, set s2)
  | Expr.InTh (t,s)           -> Tsl.InTh (tid t, setth s)
  | Expr.SubsetEqTh (s1,s2)   -> Tsl.SubsetEqTh (setth s1, setth s2)
  | Expr.InInt _              -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.SubsetEqInt _        -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.InElem (e,s)         -> Tsl.InElem (elem_to_tsl_elem e, setelem s)
  | Expr.SubsetEqElem (s1,s2) -> Tsl.SubsetEqElem (setelem s1, setelem s2)
  | Expr.Less (i1,i2)         -> Tsl.Less (integ i1, integ i2)
  | Expr.Greater (i1,i2)      -> Tsl.Greater (integ i1, integ i2)
  | Expr.LessEq (i1,i2)       -> Tsl.LessEq (integ i1, integ i2)
  | Expr.GreaterEq (i1,i2)    -> Tsl.GreaterEq (integ i1, integ i2)
  | Expr.LessTid _            -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.LessElem (e1,e2)     -> Tsl.LessElem (elem e1, elem e2)
  | Expr.GreaterElem (e1,e2)  -> Tsl.GreaterElem (elem e1, elem e2)
  | Expr.Eq (t1,t2)           -> Tsl.Eq (term t1, term t2)
  | Expr.InEq (t1,t2)         -> Tsl.InEq (term t1, term t2)
  | Expr.BoolVar v            -> Tsl.BoolVar (var_to_tsl_var v)
  | Expr.BoolArrayRd _        -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.PC (pc,t,pr)         -> Tsl.PC (pc, Option.lift tid_to_tsl_tid t,pr)
  | Expr.PCUpdate (pc,t)      -> Tsl.PCUpdate (pc, tid_to_tsl_tid t)
  | Expr.PCRange (pc1,pc2,t,pr) -> Tsl.PCRange (pc1, pc2,
                                        Option.lift tid_to_tsl_tid t,pr)


and literal_to_tsl_literal (l:Expr.literal) : Tsl.literal =
(*  LOG "Entering literal_to_tsl_literal..." LEVEL TRACE; *)
(*  LOG "literal_to_tsl_literal(%s)" (Expr.literal_to_str l) LEVEL DEBUG; *)
  match l with
    Expr.Atom a    -> Tsl.Atom (atom_to_tsl_atom a)
  | Expr.NegAtom a -> Tsl.NegAtom (atom_to_tsl_atom a)


and formula_to_tsl_formula (f:Expr.formula) : Tsl.formula =
(*  LOG "Entering formula_to_tsl_formula..." LEVEL TRACE; *)
(*  LOG "formula_to_tsl_formula(%s)" (Expr.formula_to_str f) LEVEL DEBUG; *)
  let to_formula = formula_to_tsl_formula in
  match f with
    Expr.Literal l       -> Tsl.Literal (literal_to_tsl_literal l)
  | Expr.True            -> Tsl.True
  | Expr.False           -> Tsl.False
  | Expr.And (f1,f2)     -> Tsl.And (to_formula f1, to_formula f2)
  | Expr.Or (f1,f2)      -> Tsl.Or (to_formula f1, to_formula f2)
  | Expr.Not f1          -> Tsl.Not (to_formula f1)
  | Expr.Implies (f1,f2) -> Tsl.Implies (to_formula f1, to_formula f2)
  | Expr.Iff (f1,f2)     -> Tsl.Iff (to_formula f1, to_formula f2)




(* TslExpression to Expression conversion *)


let rec tsl_sort_to_sort (s:Tsl.sort) : Expr.sort =
  match s with
  | Tsl.Set       -> Expr.Set
  | Tsl.Elem      -> Expr.Elem
  | Tsl.Thid      -> Expr.Thid
  | Tsl.Addr      -> Expr.Addr
  | Tsl.Cell      -> Expr.Cell
  | Tsl.SetTh     -> Expr.SetTh
  | Tsl.SetElem   -> Expr.SetElem
  | Tsl.Path      -> Expr.Path
  | Tsl.Mem       -> Expr.Mem
  | Tsl.Int       -> Expr.Int
  | Tsl.AddrArray -> Expr.AddrArray
  | Tsl.TidArray  -> Expr.TidArray
  | Tsl.Bool      -> Expr.Bool
  | Tsl.Unknown   -> Expr.Unknown


and var_to_expr_var (v:Tsl.variable) : Expr.variable =
  let (id,s,pr,th,p) = v
  in
    (id, tsl_sort_to_sort s, pr, Option.lift tid_to_expr_tid th, p, Expr.Normal)



and tid_to_expr_tid (th:Tsl.tid) : Expr.tid =
  match th with
  | Tsl.VarTh v            -> Expr.VarTh (var_to_expr_var v)
  | Tsl.NoThid             -> Expr.NoThid
  | Tsl.CellLockIdAt (c,l) -> Expr.CellLockIdAt (cell_to_expr_cell c,
                                                 int_to_expr_int l)
  | Tsl.ThidArrRd (tt,i)   -> Expr.ThidArrRd (tidarr_to_expr_tidarr tt,
                                              int_to_expr_int i)


and term_to_expr_term (t:Tsl.term) : Expr.term =
  match t with
  | Tsl.VarT v        -> Expr.VarT (var_to_expr_var v)
  | Tsl.SetT s        -> Expr.SetT (set_to_expr_set s)
  | Tsl.ElemT e       -> Expr.ElemT (elem_to_expr_elem e)
  | Tsl.ThidT t       -> Expr.ThidT (tid_to_expr_tid t)
  | Tsl.AddrT a       -> Expr.AddrT (addr_to_expr_addr a)
  | Tsl.CellT c       -> Expr.CellT (cell_to_expr_cell c)
  | Tsl.SetThT st     -> Expr.SetThT (setth_to_expr_setth st)
  | Tsl.SetElemT st   -> Expr.SetElemT (setelem_to_expr_setelem st)
  | Tsl.PathT p       -> Expr.PathT (path_to_expr_path p)
  | Tsl.MemT m        -> Expr.MemT (mem_to_expr_mem m)
  | Tsl.IntT i        -> Expr.IntT (int_to_expr_int i)
  | Tsl.AddrArrayT aa -> Expr.AddrArrayT (addrarr_to_expr_addrarr aa)
  | Tsl.TidArrayT tt  -> Expr.TidArrayT (tidarr_to_expr_tidarr tt)
  | Tsl.VarUpdate (v,th,t) ->
      let expr_a  = Expr.VarArray (var_to_expr_var v) in
      let expr_th = tid_to_expr_tid th in
      let expr_t  = Expr.Term (term_to_expr_term t)
      in
        Expr.ArrayT (Expr.ArrayUp (expr_a, expr_th, expr_t))



and eq_to_expr_eq ((t1,t2):Tsl.eq) : Expr.eq =
  (term_to_expr_term t1, term_to_expr_term t2)


and diseq_to_expr_diseq ((t1,t2):Tsl.diseq) : Expr.diseq =
  (term_to_expr_term t1, term_to_expr_term t2)


and set_to_expr_set (s:Tsl.set) : Expr.set =
  let to_set = set_to_expr_set in
  match s with
  | Tsl.VarSet v            -> Expr.VarSet (var_to_expr_var v)
  | Tsl.EmptySet            -> Expr.EmptySet
  | Tsl.Singl a             -> Expr.Singl (addr_to_expr_addr a)
  | Tsl.Union (s1,s2)       -> Expr.Union (to_set s1, to_set s2)
  | Tsl.Intr (s1,s2)        -> Expr.Intr (to_set s1, to_set s2)
  | Tsl.Setdiff (s1,s2)     -> Expr.Setdiff (to_set s1, to_set s2)
  | Tsl.PathToSet p         -> Expr.PathToSet (path_to_expr_path p)
  | Tsl.AddrToSet (m,a,l)   -> Expr.AddrToSetAt (mem_to_expr_mem m,
                                                 addr_to_expr_addr a,
                                                 int_to_expr_int l)


and elem_to_expr_elem (e:Tsl.elem) : Expr.elem =
  match e with
  | Tsl.VarElem v              -> Expr.VarElem (var_to_expr_var v)
  | Tsl.CellData c             -> Expr.CellData (cell_to_expr_cell c)
  | Tsl.HavocSkiplistElem      -> Expr.HavocSkiplistElem
  | Tsl.LowestElem             -> Expr.LowestElem
  | Tsl.HighestElem            -> Expr.HighestElem


and addr_to_expr_addr (a:Tsl.addr) : Expr.addr =
  match a with
  | Tsl.VarAddr v              -> Expr.VarAddr (var_to_expr_var v)
  | Tsl.Null                   -> Expr.Null
  | Tsl.NextAt (c,l)           -> Expr.NextAt (cell_to_expr_cell c, int_to_expr_int l)
  | Tsl.AddrArrRd (aa,i)       -> Expr.AddrArrRd (addrarr_to_expr_addrarr aa,
                                                  int_to_expr_int i)


and cell_to_expr_cell (c:Tsl.cell) : Expr.cell =
  match c with
    Tsl.VarCell v          -> Expr.VarCell (var_to_expr_var v)
  | Tsl.Error              -> Expr.Error
  | Tsl.MkCell (e,aa,tt,l) -> Expr.MkSLCell (elem_to_expr_elem e,
                                             addrarr_to_expr_addrarr aa,
                                             tidarr_to_expr_tidarr tt,
                                             int_to_expr_int l)
  | Tsl.CellLockAt (c,l, t)-> Expr.CellLockAt (cell_to_expr_cell c,
                                               int_to_expr_int l,
                                               tid_to_expr_tid t)
  | Tsl.CellUnlockAt (c,l) -> Expr.CellUnlockAt (cell_to_expr_cell c,
                                                 int_to_expr_int l)
  | Tsl.CellAt (m,a)       -> Expr.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


and setth_to_expr_setth (st:Tsl.setth) : Expr.setth =
  let to_setth = setth_to_expr_setth in
  match st with
  | Tsl.VarSetTh v        -> Expr.VarSetTh (var_to_expr_var v)
  | Tsl.EmptySetTh        -> Expr.EmptySetTh
  | Tsl.SinglTh t         -> Expr.SinglTh (tid_to_expr_tid t)
  | Tsl.UnionTh (s1,s2)   -> Expr.UnionTh (to_setth s1, to_setth s2)
  | Tsl.IntrTh (s1,s2)    -> Expr.IntrTh (to_setth s1, to_setth s2)
  | Tsl.SetdiffTh (s1,s2) -> Expr.SetdiffTh (to_setth s1, to_setth s2)


and setelem_to_expr_setelem (st:Tsl.setelem) : Expr.setelem =
  let to_setelem = setelem_to_expr_setelem in
  match st with
  | Tsl.VarSetElem v        -> Expr.VarSetElem (var_to_expr_var v)
  | Tsl.EmptySetElem        -> Expr.EmptySetElem
  | Tsl.SinglElem e         -> Expr.SinglElem (elem_to_expr_elem e)
  | Tsl.UnionElem (s1,s2)   -> Expr.UnionElem (to_setelem s1, to_setelem s2)
  | Tsl.IntrElem (s1,s2)    -> Expr.IntrElem (to_setelem s1, to_setelem s2)
  | Tsl.SetdiffElem (s1,s2) -> Expr.SetdiffElem (to_setelem s1, to_setelem s2)
  | Tsl.SetToElems (s,m)    -> Expr.SetToElems (set_to_expr_set s,
                                                mem_to_expr_mem m)


and path_to_expr_path (p:Tsl.path) : Expr.path =
  match p with
  | Tsl.VarPath v             -> Expr.VarPath (var_to_expr_var v)
  | Tsl.Epsilon               -> Expr.Epsilon
  | Tsl.SimplePath a          -> Expr.SimplePath (addr_to_expr_addr a)
  | Tsl.GetPath (m,a1,a2,l)   -> Expr.GetPathAt (mem_to_expr_mem m,
                                                 addr_to_expr_addr a1,
                                                 addr_to_expr_addr a2,
                                                 int_to_expr_int l)


and mem_to_expr_mem (m:Tsl.mem) : Expr.mem =
  match m with
  | Tsl.VarMem v       -> Expr.VarMem (var_to_expr_var v)
  | Tsl.Update (m,a,c) -> Expr.Update (mem_to_expr_mem m,
                                       addr_to_expr_addr a,
                                       cell_to_expr_cell c)


and int_to_expr_int (i:Tsl.integer) : Expr.integer =
  match i with
  | Tsl.IntVal i       -> Expr.IntVal i
  | Tsl.VarInt v       -> Expr.VarInt (var_to_expr_var v)
  | Tsl.IntNeg i       -> Expr.IntNeg (int_to_expr_int i)
  | Tsl.IntAdd (i1,i2) -> Expr.IntAdd (int_to_expr_int i1, int_to_expr_int i2)
  | Tsl.IntSub (i1,i2) -> Expr.IntSub (int_to_expr_int i1, int_to_expr_int i2)
  | Tsl.IntMul (i1,i2) -> Expr.IntMul (int_to_expr_int i1, int_to_expr_int i2)
  | Tsl.IntDiv (i1,i2) -> Expr.IntDiv (int_to_expr_int i1, int_to_expr_int i2)
  | Tsl.CellMax (c)    -> Expr.CellMax (cell_to_expr_cell c)
  | Tsl.HavocLevel     -> Expr.HavocLevel


and addrarr_to_expr_addrarr (arr:Tsl.addrarr) : Expr.addrarr =
  match arr with
  | Tsl.VarAddrArray v       -> Expr.VarAddrArray (var_to_expr_var v)
  | Tsl.AddrArrayUp (aa,i,a) -> Expr.AddrArrayUp (addrarr_to_expr_addrarr aa,
                                                  int_to_expr_int i,
                                                  addr_to_expr_addr a)
  | Tsl.CellArr c            -> Expr.CellArr (cell_to_expr_cell c)


and tidarr_to_expr_tidarr (arr:Tsl.tidarr) : Expr.tidarr =
  match arr with
  | Tsl.VarTidArray v       -> Expr.VarTidArray (var_to_expr_var v)
  | Tsl.TidArrayUp (tt,i,t) -> Expr.TidArrayUp (tidarr_to_expr_tidarr tt,
                                                int_to_expr_int i,
                                                tid_to_expr_tid t)
  | Tsl.CellTids c          -> Expr.CellTids (cell_to_expr_cell c)


and tsl_atom_to_atom (a:Tsl.atom) : Expr.atom =
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
    Tsl.Append (p1,p2,p3)    -> Expr.Append (path p1,path p2,path p3)
  | Tsl.Reach (m,a1,a2,l,p  )-> Expr.ReachAt (mem m, addr a1, addr a2,
                                            integ l, path p)
  | Tsl.OrderList(m,a1,a2)   -> Expr.OrderList (mem m, addr a1, addr a2)
  | Tsl.Skiplist(m,s,l,a1,a2)-> Expr.Skiplist (mem m, set s, integ l,
                                               addr a1, addr a2)
  | Tsl.In (a,s)             -> Expr.In (addr a, set s)
  | Tsl.SubsetEq (s1,s2)     -> Expr.SubsetEq (set s1, set s2)
  | Tsl.InTh (t,s)           -> Expr.InTh (tid t, setth s)
  | Tsl.SubsetEqTh (s1,s2)   -> Expr.SubsetEqTh (setth s1, setth s2)
  | Tsl.InElem (e,s)         -> Expr.InElem (elem_to_expr_elem e, setelem s)
  | Tsl.SubsetEqElem (s1,s2) -> Expr.SubsetEqElem (setelem s1, setelem s2)
  | Tsl.Less (i1,i2)         -> Expr.Less (integ i1, integ i2)
  | Tsl.Greater (i1,i2)      -> Expr.Greater (integ i1, integ i2)
  | Tsl.LessEq (i1,i2)       -> Expr.LessEq (integ i1, integ i2)
  | Tsl.GreaterEq (i1,i2)    -> Expr.GreaterEq (integ i1, integ i2)
  | Tsl.LessElem (e1,e2)     -> Expr.LessElem (elem e1, elem e2)
  | Tsl.GreaterElem (e1,e2)  -> Expr.GreaterElem (elem e1, elem e2)
  | Tsl.Eq (t1,t2)           -> Expr.Eq (term t1, term t2)
  | Tsl.InEq (t1,t2)         -> Expr.InEq (term t1, term t2)
  | Tsl.BoolVar v            -> Expr.BoolVar (var_to_expr_var v)
  | Tsl.PC (pc,t,pr)         -> Expr.PC (pc, Option.lift tid_to_expr_tid t,pr)
  | Tsl.PCUpdate (pc,t)      -> Expr.PCUpdate (pc, tid_to_expr_tid t)
  | Tsl.PCRange (pc1,pc2,t,pr) -> Expr.PCRange (pc1, pc2,
                                        Option.lift tid_to_expr_tid t,pr)


and literal_to_expr_literal (l:Tsl.literal) : Expr.literal =
  match l with
    Tsl.Atom a    -> Expr.Atom (tsl_atom_to_atom a)
  | Tsl.NegAtom a -> Expr.NegAtom (tsl_atom_to_atom a)


and formula_to_expr_formula (f:Tsl.formula) : Expr.formula =
  let to_formula = formula_to_expr_formula in
  match f with
    Tsl.Literal l       -> Expr.Literal (literal_to_expr_literal l)
  | Tsl.True            -> Expr.True
  | Tsl.False           -> Expr.False
  | Tsl.And (f1,f2)     -> Expr.And (to_formula f1, to_formula f2)
  | Tsl.Or (f1,f2)      -> Expr.Or (to_formula f1, to_formula f2)
  | Tsl.Not f1          -> Expr.Not (to_formula f1)
  | Tsl.Implies (f1,f2) -> Expr.Implies (to_formula f1, to_formula f2)
  | Tsl.Iff (f1,f2)     -> Expr.Iff (to_formula f1, to_formula f2)
