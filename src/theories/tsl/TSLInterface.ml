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
  | Expr.ArrayT a      -> arrays_to_tsl_term a 


and arrays_to_tsl_term (a:Expr.arrays) : Tsl.term =
  match a with
    Expr.VarArray v -> build_term_var v
  | Expr.ArrayUp (Expr.VarArray v,th_p,Expr.Term t) ->
      let tsl_v  = variable_to_tsl_var v in
      let tsl_th = tid_to_tsl_tid th_p in
      let tsl_t  = term_to_tsl_term t
      in
        Tsl.VarUpdate (tsl_v, tsl_th, tsl_t)
  | Expr.ArrayUp (_,_,e) -> raise(UnsupportedTslExpr(Expr.expr_to_str e))



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
  | Expr.CellLockAt (c,l)     -> Tsl.CellLockAt (cell_to_tsl_cell c,
                                                 int_to_tsl_int l,
                                                 Tsl.NoThid)
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


and tidarr_to_tsl_tidarr (arr:Expr.tidarr) : Tsl.tidarr =
  match arr with
    Expr.VarTidArray v       -> Tsl.VarTidArray (variable_to_tsl_var v)
  | Expr.TidArrayUp (tt,i,t) -> Tsl.TidArrayUp (tidarr_to_tsl_tidarr tt,
                                                int_to_tsl_int i,
                                                tid_to_tsl_tid t)


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
