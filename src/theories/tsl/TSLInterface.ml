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
  match s with
    Expr.Set       -> Tsl.Set
  | Expr.Elem      -> Tsl.Elem
  | Expr.Thid      -> Tsl.Thid
  | Expr.Addr      -> Tsl.Addr
  | Expr.Cell      -> Tsl.Cell
  | Expr.SetTh     -> Tsl.SetTh
  | Expr.SetInt    -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.SetElem   -> Tsl.SetElem
  | Expr.Path      -> Tsl.Path
  | Expr.Mem       -> Tsl.Mem
  | Expr.Bool      -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Int       -> Tsl.Int
  | Expr.Array     -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.AddrArray -> Tsl.AddrArray
  | Expr.TidArray  -> Tsl.TidArray
  | Expr.Unknown   -> Tsl.Unknown



and build_term_var (v:Expr.variable) : Tsl.term =
  let tsl_v = variable_to_tsl_var v in
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



and variable_to_tsl_var (v:Expr.variable) : Tsl.variable =
  let (id,s,pr,th,p,_) = v
  in
    (id, sort_to_tsl_sort s, pr, Option.lift tid_to_tsl_tid th, p)



and tid_to_tsl_tid (th:Expr.tid) : Tsl.tid =
  match th with
    Expr.VarTh v        -> Tsl.VarTh (variable_to_tsl_var v)
  | Expr.NoThid         -> Tsl.NoThid
  | Expr.CellLockId _   -> raise (UnsupportedTslExpr(Expr.tid_to_str th))
  | Expr.CellLockIdAt (c,l) -> Tsl.CellLockIdAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l)
  | Expr.ThidArrayRd _      -> raise (UnsupportedTslExpr(Expr.tid_to_str th))
  | Expr.ThidArrRd (tt,i)   -> Tsl.ThidArrRd (tidarr_to_tsl_tidarr tt,
                                              int_to_tsl_int i)

and term_to_tsl_term (t:Expr.term) : Tsl.term =
  match t with
    Expr.VarT v        -> Tsl.VarT (variable_to_tsl_var v)
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
  | Expr.ArrayT a      -> raise(UnsupportedTslExpr(Expr.term_to_str t))


and eq_to_tsl_eq ((t1,t2):Expr.eq) : Tsl.eq =
  (term_to_tsl_term t1, term_to_tsl_term t2)


and diseq_to_tsl_eq ((t1,t2):Expr.diseq) : Tsl.diseq =
  (term_to_tsl_term t1, term_to_tsl_term t2)


and set_to_tsl_set (s:Expr.set) : Tsl.set =
  let to_set = set_to_tsl_set in
  match s with
    Expr.VarSet v            -> Tsl.VarSet (variable_to_tsl_var v)
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
      Tsl.VarSet (variable_to_tsl_var v)
  | Expr.SetArrayRd _        -> raise(UnsupportedTslExpr(Expr.set_to_str s))


and elem_to_tsl_elem (e:Expr.elem) : Tsl.elem =
  match e with
    Expr.VarElem v              -> Tsl.VarElem (variable_to_tsl_var v)
  | Expr.CellData c             -> Tsl.CellData (cell_to_tsl_cell c)
  | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarElem (variable_to_tsl_var v)
  | Expr.ElemArrayRd _          -> raise(UnsupportedTslExpr(Expr.elem_to_str e))
  | Expr.HavocListElem          -> raise(UnsupportedTslExpr(Expr.elem_to_str e))
  | Expr.HavocSkiplistElem      -> Tsl.HavocSkiplistElem
  | Expr.LowestElem             -> Tsl.LowestElem
  | Expr.HighestElem            -> Tsl.HighestElem


and addr_to_tsl_addr (a:Expr.addr) : Tsl.addr =
  match a with
    Expr.VarAddr v              -> Tsl.VarAddr (variable_to_tsl_var v)
  | Expr.Null                   -> Tsl.Null
  | Expr.Next _                 -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.NextAt (c,l)           -> Tsl.NextAt (cell_to_tsl_cell c, int_to_tsl_int l)
  | Expr.FirstLocked _          -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.FirstLockedAt _        -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarAddr (variable_to_tsl_var v)
  | Expr.AddrArrayRd _          -> raise(UnsupportedTslExpr(Expr.addr_to_str a))
  | Expr.AddrArrRd (aa,i)       -> Tsl.AddrArrRd (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i)


and cell_to_tsl_cell (c:Expr.cell) : Tsl.cell =
  match c with
    Expr.VarCell v            -> Tsl.VarCell (variable_to_tsl_var v)
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
      Tsl.VarCell (variable_to_tsl_var v)
  | Expr.CellArrayRd _        -> raise(UnsupportedTslExpr(Expr.cell_to_str c))


and setth_to_tsl_setth (st:Expr.setth) : Tsl.setth =
  let to_setth = setth_to_tsl_setth in
  match st with
    Expr.VarSetTh v        -> Tsl.VarSetTh (variable_to_tsl_var v)
  | Expr.EmptySetTh        -> Tsl.EmptySetTh
  | Expr.SinglTh t         -> Tsl.SinglTh (tid_to_tsl_tid t)
  | Expr.UnionTh (s1,s2)   -> Tsl.UnionTh (to_setth s1, to_setth s2)
  | Expr.IntrTh (s1,s2)    -> Tsl.IntrTh (to_setth s1, to_setth s2)
  | Expr.SetdiffTh (s1,s2) -> Tsl.SetdiffTh (to_setth s1, to_setth s2)
  | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarSetTh (variable_to_tsl_var v)
  | Expr.SetThArrayRd _    -> raise(UnsupportedTslExpr
                                            (Expr.setth_to_str st))


and setelem_to_tsl_setelem (st:Expr.setelem) : Tsl.setelem =
  let to_setelem = setelem_to_tsl_setelem in
  match st with
    Expr.VarSetElem v        -> Tsl.VarSetElem (variable_to_tsl_var v)
  | Expr.EmptySetElem        -> Tsl.EmptySetElem
  | Expr.SinglElem e         -> Tsl.SinglElem (elem_to_tsl_elem e)
  | Expr.UnionElem (s1,s2)   -> Tsl.UnionElem (to_setelem s1, to_setelem s2)
  | Expr.IntrElem (s1,s2)    -> Tsl.IntrElem (to_setelem s1, to_setelem s2)
  | Expr.SetdiffElem (s1,s2) -> Tsl.SetdiffElem (to_setelem s1, to_setelem s2)
  | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarSetElem (variable_to_tsl_var v)
  | Expr.SetToElems (s,m)    -> Tsl.SetToElems (set_to_tsl_set s,
                                                mem_to_tsl_mem m)
  | Expr.SetElemArrayRd _    -> raise(UnsupportedTslExpr
                                            (Expr.setelem_to_str st))


and path_to_tsl_path (p:Expr.path) : Tsl.path =
  match p with
    Expr.VarPath v             -> Tsl.VarPath (variable_to_tsl_var v)
  | Expr.Epsilon               -> Tsl.Epsilon
  | Expr.SimplePath a          -> Tsl.SimplePath (addr_to_tsl_addr a)
  | Expr.GetPath _             -> raise(UnsupportedTslExpr(Expr.path_to_str p))
  | Expr.GetPathAt (m,a1,a2,l) -> Tsl.GetPath (mem_to_tsl_mem m,
                                               addr_to_tsl_addr a1,
                                               addr_to_tsl_addr a2,
                                               int_to_tsl_int l)
  | Expr.PathArrayRd _         -> raise(UnsupportedTslExpr(Expr.path_to_str p))


and mem_to_tsl_mem (m:Expr.mem) : Tsl.mem =
  match m with
    Expr.VarMem v       -> Tsl.VarMem (variable_to_tsl_var v)
  | Expr.Update (m,a,c) -> Tsl.Update (mem_to_tsl_mem m,
                                       addr_to_tsl_addr a,
                                       cell_to_tsl_cell c)
  (* Missing the case for "emp" *)
  | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tsl.VarMem (variable_to_tsl_var v)
  | Expr.MemArrayRd _        -> raise (UnsupportedTslExpr (Expr.mem_to_str m))


and int_to_tsl_int (i:Expr.integer) : Tsl.integer =
  match i with
    Expr.IntVal i       -> Tsl.IntVal i
  | Expr.VarInt v       -> Tsl.VarInt (variable_to_tsl_var v)
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
  match arr with
    Expr.VarAddrArray v       -> Tsl.VarAddrArray (variable_to_tsl_var v)
  | Expr.AddrArrayUp (aa,i,a) -> Tsl.AddrArrayUp (addrarr_to_tsl_addrarr aa,
                                                  int_to_tsl_int i,
                                                  addr_to_tsl_addr a)
  | Expr.CellArr c            -> Tsl.CellArr (cell_to_tsl_cell c)


and tidarr_to_tsl_tidarr (arr:Expr.tidarr) : Tsl.tidarr =
  match arr with
    Expr.VarTidArray v       -> Tsl.VarTidArray (variable_to_tsl_var v)
  | Expr.TidArrayUp (tt,i,t) -> Tsl.TidArrayUp (tidarr_to_tsl_tidarr tt,
                                                int_to_tsl_int i,
                                                tid_to_tsl_tid t)
  | Expr.CellTids c          -> Tsl.CellTids (cell_to_tsl_cell c)


and atom_to_tsl_atom (a:Expr.atom) : Tsl.atom =
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
  | Expr.BoolVar _            -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.BoolArrayRd _        -> raise(UnsupportedTslExpr(Expr.atom_to_str a))
  | Expr.PC (pc,t,pr)         -> Tsl.PC (pc, Option.lift tid_to_tsl_tid t,pr)
  | Expr.PCUpdate (pc,t)      -> Tsl.PCUpdate (pc, tid_to_tsl_tid t)
  | Expr.PCRange (pc1,pc2,t,pr) -> Tsl.PCRange (pc1, pc2,
                                        Option.lift tid_to_tsl_tid t,pr)


and literal_to_tsl_literal (l:Expr.literal) : Tsl.literal =
  match l with
    Expr.Atom a    -> Tsl.Atom (atom_to_tsl_atom a)
  | Expr.NegAtom a -> Tsl.NegAtom (atom_to_tsl_atom a)


and formula_to_tsl_formula (f:Expr.formula) : Tsl.formula =
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
  | Tsl.Unknown   -> Expr.Unknown


and tsl_variable_to_var (v:Tsl.variable) : Expr.variable =
  let (id,s,pr,th,p) = v
  in
    (id, tsl_sort_to_sort s, pr, Option.lift tsl_tid_to_tid th, p, Expr.Normal)



and tsl_tid_to_tid (th:Tsl.tid) : Expr.tid =
  match th with
  | Tsl.VarTh v            -> Expr.VarTh (tsl_variable_to_var v)
  | Tsl.NoThid             -> Expr.NoThid
  | Tsl.CellLockIdAt (c,l) -> Expr.CellLockIdAt (tsl_cell_to_cell c,
                                                 tsl_int_to_int l)
  | Tsl.ThidArrRd (tt,i)   -> Expr.ThidArrRd (tsl_tidarr_to_tidarr tt,
                                              tsl_int_to_int i)


and tsl_term_to_term (t:Tsl.term) : Expr.term =
  match t with
  | Tsl.VarT v        -> Expr.VarT (tsl_variable_to_var v)
  | Tsl.SetT s        -> Expr.SetT (tsl_set_to_set s)
  | Tsl.ElemT e       -> Expr.ElemT (tsl_elem_to_elem e)
  | Tsl.ThidT t       -> Expr.ThidT (tsl_tid_to_tid t)
  | Tsl.AddrT a       -> Expr.AddrT (tsl_addr_to_addr a)
  | Tsl.CellT c       -> Expr.CellT (tsl_cell_to_cell c)
  | Tsl.SetThT st     -> Expr.SetThT (tsl_setth_to_setth st)
  | Tsl.SetElemT st   -> Expr.SetElemT (tsl_setelem_to_setelem st)
  | Tsl.PathT p       -> Expr.PathT (tsl_path_to_path p)
  | Tsl.MemT m        -> Expr.MemT (tsl_mem_to_mem m)
  | Tsl.IntT i        -> Expr.IntT (tsl_int_to_int i)
  | Tsl.AddrArrayT aa -> Expr.AddrArrayT (tsl_addrarr_to_addrarr aa)
  | Tsl.TidArrayT tt  -> Expr.TidArrayT (tsl_tidarr_to_tidarr tt)



and tsl_eq_to_eq ((t1,t2):Tsl.eq) : Expr.eq =
  (tsl_term_to_term t1, tsl_term_to_term t2)


and tsl_diseq_to_eq ((t1,t2):Tsl.diseq) : Expr.diseq =
  (tsl_term_to_term t1, tsl_term_to_term t2)


and tsl_set_to_set (s:Tsl.set) : Expr.set =
  let to_set = tsl_set_to_set in
  match s with
  | Tsl.VarSet v            -> Expr.VarSet (tsl_variable_to_var v)
  | Tsl.EmptySet            -> Expr.EmptySet
  | Tsl.Singl a             -> Expr.Singl (tsl_addr_to_addr a)
  | Tsl.Union (s1,s2)       -> Expr.Union (to_set s1, to_set s2)
  | Tsl.Intr (s1,s2)        -> Expr.Intr (to_set s1, to_set s2)
  | Tsl.Setdiff (s1,s2)     -> Expr.Setdiff (to_set s1, to_set s2)
  | Tsl.PathToSet p         -> Expr.PathToSet (tsl_path_to_path p)
  | Tsl.AddrToSet (m,a,l)   -> Expr.AddrToSetAt (tsl_mem_to_mem m,
                                                 tsl_addr_to_addr a,
                                                 tsl_int_to_int l)


and tsl_elem_to_elem (e:Tsl.elem) : Expr.elem =
  match e with
  | Tsl.VarElem v              -> Expr.VarElem (tsl_variable_to_var v)
  | Tsl.CellData c             -> Expr.CellData (tsl_cell_to_cell c)
  | Tsl.HavocSkiplistElem      -> Expr.HavocSkiplistElem
  | Tsl.LowestElem             -> Expr.LowestElem
  | Tsl.HighestElem            -> Expr.HighestElem


and tsl_addr_to_addr (a:Tsl.addr) : Expr.addr =
  match a with
  | Tsl.VarAddr v              -> Expr.VarAddr (tsl_variable_to_var v)
  | Tsl.Null                   -> Expr.Null
  | Tsl.NextAt (c,l)           -> Expr.NextAt (tsl_cell_to_cell c, tsl_int_to_int l)
  | Tsl.AddrArrRd (aa,i)       -> Expr.AddrArrRd (tsl_addrarr_to_addrarr aa,
                                                  tsl_int_to_int i)


and tsl_cell_to_cell (c:Tsl.cell) : Expr.cell =
  match c with
    Tsl.VarCell v          -> Expr.VarCell (tsl_variable_to_var v)
  | Tsl.Error              -> Expr.Error
  | Tsl.MkCell (e,aa,tt,l) -> Expr.MkSLCell (tsl_elem_to_elem e,
                                             tsl_addrarr_to_addrarr aa,
                                             tsl_tidarr_to_tidarr tt,
                                             tsl_int_to_int l)
  | Tsl.CellLockAt (c,l, t)-> Expr.CellLockAt (tsl_cell_to_cell c,
                                               tsl_int_to_int l,
                                               tsl_tid_to_tid t)
  | Tsl.CellUnlockAt (c,l) -> Expr.CellUnlockAt (tsl_cell_to_cell c,
                                                 tsl_int_to_int l)
  | Tsl.CellAt (m,a)       -> Expr.CellAt (tsl_mem_to_mem m, tsl_addr_to_addr a)


and tsl_setth_to_setth (st:Tsl.setth) : Expr.setth =
  let to_setth = tsl_setth_to_setth in
  match st with
  | Tsl.VarSetTh v        -> Expr.VarSetTh (tsl_variable_to_var v)
  | Tsl.EmptySetTh        -> Expr.EmptySetTh
  | Tsl.SinglTh t         -> Expr.SinglTh (tsl_tid_to_tid t)
  | Tsl.UnionTh (s1,s2)   -> Expr.UnionTh (to_setth s1, to_setth s2)
  | Tsl.IntrTh (s1,s2)    -> Expr.IntrTh (to_setth s1, to_setth s2)
  | Tsl.SetdiffTh (s1,s2) -> Expr.SetdiffTh (to_setth s1, to_setth s2)


and tsl_setelem_to_setelem (st:Tsl.setelem) : Expr.setelem =
  let to_setelem = tsl_setelem_to_setelem in
  match st with
  | Tsl.VarSetElem v        -> Expr.VarSetElem (tsl_variable_to_var v)
  | Tsl.EmptySetElem        -> Expr.EmptySetElem
  | Tsl.SinglElem e         -> Expr.SinglElem (tsl_elem_to_elem e)
  | Tsl.UnionElem (s1,s2)   -> Expr.UnionElem (to_setelem s1, to_setelem s2)
  | Tsl.IntrElem (s1,s2)    -> Expr.IntrElem (to_setelem s1, to_setelem s2)
  | Tsl.SetdiffElem (s1,s2) -> Expr.SetdiffElem (to_setelem s1, to_setelem s2)
  | Tsl.SetToElems (s,m)    -> Expr.SetToElems (tsl_set_to_set s,
                                                tsl_mem_to_mem m)


and tsl_path_to_path (p:Tsl.path) : Expr.path =
  match p with
  | Tsl.VarPath v             -> Expr.VarPath (tsl_variable_to_var v)
  | Tsl.Epsilon               -> Expr.Epsilon
  | Tsl.SimplePath a          -> Expr.SimplePath (tsl_addr_to_addr a)
  | Tsl.GetPath (m,a1,a2,l)   -> Expr.GetPathAt (tsl_mem_to_mem m,
                                                 tsl_addr_to_addr a1,
                                                 tsl_addr_to_addr a2,
                                                 tsl_int_to_int l)


and tsl_mem_to_mem (m:Tsl.mem) : Expr.mem =
  match m with
  | Tsl.VarMem v       -> Expr.VarMem (tsl_variable_to_var v)
  | Tsl.Update (m,a,c) -> Expr.Update (tsl_mem_to_mem m,
                                       tsl_addr_to_addr a,
                                       tsl_cell_to_cell c)


and tsl_int_to_int (i:Tsl.integer) : Expr.integer =
  match i with
  | Tsl.IntVal i       -> Expr.IntVal i
  | Tsl.VarInt v       -> Expr.VarInt (tsl_variable_to_var v)
  | Tsl.IntNeg i       -> Expr.IntNeg (tsl_int_to_int i)
  | Tsl.IntAdd (i1,i2) -> Expr.IntAdd (tsl_int_to_int i1, tsl_int_to_int i2)
  | Tsl.IntSub (i1,i2) -> Expr.IntSub (tsl_int_to_int i1, tsl_int_to_int i2)
  | Tsl.IntMul (i1,i2) -> Expr.IntMul (tsl_int_to_int i1, tsl_int_to_int i2)
  | Tsl.IntDiv (i1,i2) -> Expr.IntDiv (tsl_int_to_int i1, tsl_int_to_int i2)
  | Tsl.CellMax (c)    -> Expr.CellMax (tsl_cell_to_cell c)
  | Tsl.HavocLevel     -> Expr.HavocLevel


and tsl_addrarr_to_addrarr (arr:Tsl.addrarr) : Expr.addrarr =
  match arr with
  | Tsl.VarAddrArray v       -> Expr.VarAddrArray (tsl_variable_to_var v)
  | Tsl.AddrArrayUp (aa,i,a) -> Expr.AddrArrayUp (tsl_addrarr_to_addrarr aa,
                                                  tsl_int_to_int i,
                                                  tsl_addr_to_addr a)
  | Tsl.CellArr c            -> Expr.CellArr (tsl_cell_to_cell c)


and tsl_tidarr_to_tidarr (arr:Tsl.tidarr) : Expr.tidarr =
  match arr with
  | Tsl.VarTidArray v       -> Expr.VarTidArray (tsl_variable_to_var v)
  | Tsl.TidArrayUp (tt,i,t) -> Expr.TidArrayUp (tsl_tidarr_to_tidarr tt,
                                                tsl_int_to_int i,
                                                tsl_tid_to_tid t)
  | Tsl.CellTids c          -> Expr.CellTids (tsl_cell_to_cell c)


and tsl_atom_to_atom (a:Tsl.atom) : Expr.atom =
  let path    = tsl_path_to_path       in
  let mem     = tsl_mem_to_mem         in
  let addr    = tsl_addr_to_addr       in
  let elem    = tsl_elem_to_elem       in
  let set     = tsl_set_to_set         in
  let tid     = tsl_tid_to_tid         in
  let setth   = tsl_setth_to_setth     in
  let setelem = tsl_setelem_to_setelem in
  let integ   = tsl_int_to_int         in
  let term    = tsl_term_to_term       in
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
  | Tsl.InElem (e,s)         -> Expr.InElem (tsl_elem_to_elem e, setelem s)
  | Tsl.SubsetEqElem (s1,s2) -> Expr.SubsetEqElem (setelem s1, setelem s2)
  | Tsl.Less (i1,i2)         -> Expr.Less (integ i1, integ i2)
  | Tsl.Greater (i1,i2)      -> Expr.Greater (integ i1, integ i2)
  | Tsl.LessEq (i1,i2)       -> Expr.LessEq (integ i1, integ i2)
  | Tsl.GreaterEq (i1,i2)    -> Expr.GreaterEq (integ i1, integ i2)
  | Tsl.LessElem (e1,e2)     -> Expr.LessElem (elem e1, elem e2)
  | Tsl.GreaterElem (e1,e2)  -> Expr.GreaterElem (elem e1, elem e2)
  | Tsl.Eq (t1,t2)           -> Expr.Eq (term t1, term t2)
  | Tsl.InEq (t1,t2)         -> Expr.InEq (term t1, term t2)
  | Tsl.PC (pc,t,pr)         -> Expr.PC (pc, Option.lift tsl_tid_to_tid t,pr)
  | Tsl.PCUpdate (pc,t)      -> Expr.PCUpdate (pc, tsl_tid_to_tid t)
  | Tsl.PCRange (pc1,pc2,t,pr) -> Expr.PCRange (pc1, pc2,
                                        Option.lift tsl_tid_to_tid t,pr)


and tsl_literal_to_literal (l:Tsl.literal) : Expr.literal =
  match l with
    Tsl.Atom a    -> Expr.Atom (tsl_atom_to_atom a)
  | Tsl.NegAtom a -> Expr.NegAtom (tsl_atom_to_atom a)


and tsl_formula_to_formula (f:Tsl.formula) : Expr.formula =
  let to_formula = tsl_formula_to_formula in
  match f with
    Tsl.Literal l       -> Expr.Literal (tsl_literal_to_literal l)
  | Tsl.True            -> Expr.True
  | Tsl.False           -> Expr.False
  | Tsl.And (f1,f2)     -> Expr.And (to_formula f1, to_formula f2)
  | Tsl.Or (f1,f2)      -> Expr.Or (to_formula f1, to_formula f2)
  | Tsl.Not f1          -> Expr.Not (to_formula f1)
  | Tsl.Implies (f1,f2) -> Expr.Implies (to_formula f1, to_formula f2)
  | Tsl.Iff (f1,f2)     -> Expr.Iff (to_formula f1, to_formula f2)
