open LeapLib

module Expr=Expression
module Tll=TllExpression


type varId = Expr.varId
type sort  = Expr.sort
type tid   = Expr.tid

exception UnsupportedSort of string
exception UnsupportedTllExpr of string



(* Expression to TllExpression conversion *)


let rec sort_to_tll_sort (s:Expr.sort) : Tll.sort =
  match s with
  | Expr.Set       -> Tll.Set
  | Expr.Elem      -> Tll.Elem
  | Expr.Thid      -> Tll.Thid
  | Expr.Addr      -> Tll.Addr
  | Expr.Cell      -> Tll.Cell
  | Expr.SetTh     -> Tll.SetTh
  | Expr.SetInt    -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.SetElem   -> Tll.SetElem
  | Expr.Path      -> Tll.Path
  | Expr.Mem       -> Tll.Mem
  | Expr.Bool      -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Int       -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Array     -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.AddrArray -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.TidArray  -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Unknown   -> Tll.Unknown


and sort_to_expr_sort (s:Tll.sort) : Expr.sort =
  match s with
  | Tll.Set     -> Expr.Set
  | Tll.Elem    -> Expr.Elem
  | Tll.Thid    -> Expr.Thid
  | Tll.Addr    -> Expr.Addr
  | Tll.Cell    -> Expr.Cell
  | Tll.SetTh   -> Expr.SetTh
  | Tll.SetElem -> Expr.SetElem
  | Tll.Path    -> Expr.Path
  | Tll.Mem     -> Expr.Mem
  | Tll.Unknown -> Expr.Unknown


and build_term_var (v:Expr.variable) : Tll.term =
  let tll_v = variable_to_tll_var v in
  match Expr.var_sort v with
    Expr.Set   -> Tll.SetT   (Tll.VarSet   tll_v)
  | Expr.Elem  -> Tll.ElemT  (Tll.VarElem  tll_v)
  | Expr.Thid  -> Tll.ThidT  (Tll.VarTh    tll_v)
  | Expr.Addr  -> Tll.AddrT  (Tll.VarAddr  tll_v)
  | Expr.Cell  -> Tll.CellT  (Tll.VarCell  tll_v)
  | Expr.SetTh -> Tll.SetThT (Tll.VarSetTh tll_v)
  | Expr.Path  -> Tll.PathT  (Tll.VarPath  tll_v)
  | Expr.Mem   -> Tll.MemT   (Tll.VarMem   tll_v)
  | _          -> Tll.VarT   (tll_v)



and variable_to_tll_var (v:Expr.variable) : Tll.variable =
  let (id,s,pr,th,p,_) = v
  in
    (id, sort_to_tll_sort s, pr, Option.lift tid_to_tll_tid th, p)



and tid_to_tll_tid (th:Expr.tid) : Tll.tid =
  match th with
    Expr.VarTh v        -> Tll.VarTh (variable_to_tll_var v)
  | Expr.NoThid         -> Tll.NoThid
  | Expr.CellLockId c   -> Tll.CellLockId (cell_to_tll_cell c)
  | Expr.CellLockIdAt _ -> raise (UnsupportedTllExpr(Expr.tid_to_str th))
  | Expr.ThidArrayRd _  -> raise (UnsupportedTllExpr(Expr.tid_to_str th))
  | Expr.ThidArrRd _    -> raise (UnsupportedTllExpr(Expr.tid_to_str th))


and term_to_tll_term (t:Expr.term) : Tll.term =
  match t with
    Expr.VarT v       -> Tll.VarT (variable_to_tll_var v)
  | Expr.SetT s       -> Tll.SetT (set_to_tll_set s)
  | Expr.ElemT e      -> Tll.ElemT (elem_to_tll_elem e)
  | Expr.ThidT t      -> Tll.ThidT (tid_to_tll_tid t)
  | Expr.AddrT a      -> Tll.AddrT (addr_to_tll_addr a)
  | Expr.CellT c      -> Tll.CellT (cell_to_tll_cell c)
  | Expr.SetThT st    -> Tll.SetThT (setth_to_tll_setth st)
  | Expr.SetIntT _    -> raise(UnsupportedTllExpr(Expr.term_to_str t))
  | Expr.SetElemT st  -> Tll.SetElemT (setelem_to_tll_setelem st)
  | Expr.PathT p      -> Tll.PathT (path_to_tll_path p)
  | Expr.MemT m       -> Tll.MemT (mem_to_tll_mem m)
  | Expr.IntT _       -> raise(UnsupportedTllExpr (Expr.term_to_str t))
  | Expr.AddrArrayT a -> raise(UnsupportedTllExpr (Expr.term_to_str t))
  | Expr.TidArrayT a  -> raise(UnsupportedTllExpr (Expr.term_to_str t))
  | Expr.ArrayT a     -> arrays_to_tll_term a 


and arrays_to_tll_term (a:Expr.arrays) : Tll.term =
  match a with
    Expr.VarArray v -> build_term_var v
  | Expr.ArrayUp (Expr.VarArray v,th_p,Expr.Term t) ->
      let tll_v  = variable_to_tll_var v in
      let tll_th = tid_to_tll_tid th_p in
      let tll_t  = term_to_tll_term t
      in
        Tll.VarUpdate (tll_v, tll_th, tll_t)
  | Expr.ArrayUp (_,_,e) -> raise(UnsupportedTllExpr(Expr.expr_to_str e))



and eq_to_tll_eq ((t1,t2):Expr.eq) : Tll.eq =
  (term_to_tll_term t1, term_to_tll_term t2)


and diseq_to_tll_eq ((t1,t2):Expr.diseq) : Tll.diseq =
  (term_to_tll_term t1, term_to_tll_term t2)


and set_to_tll_set (s:Expr.set) : Tll.set =
  let to_set = set_to_tll_set in
  match s with
    Expr.VarSet v        -> Tll.VarSet (variable_to_tll_var v)
  | Expr.EmptySet        -> Tll.EmptySet
  | Expr.Singl a         -> Tll.Singl (addr_to_tll_addr a)
  | Expr.Union (s1,s2)   -> Tll.Union (to_set s1, to_set s2)
  | Expr.Intr (s1,s2)    -> Tll.Intr (to_set s1, to_set s2)
  | Expr.Setdiff (s1,s2) -> Tll.Setdiff (to_set s1, to_set s2)
  | Expr.PathToSet p     -> Tll.PathToSet (path_to_tll_path p)
  | Expr.AddrToSet (m,a) -> Tll.AddrToSet (mem_to_tll_mem m, addr_to_tll_addr a)
  | Expr.AddrToSetAt _   -> raise(UnsupportedTllExpr(Expr.set_to_str s))
  | Expr.SetArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarSet (variable_to_tll_var v)
  | Expr.SetArrayRd _          -> raise (UnsupportedTllExpr (Expr.set_to_str s))


and elem_to_tll_elem (e:Expr.elem) : Tll.elem =
  match e with
    Expr.VarElem v              -> Tll.VarElem (variable_to_tll_var v)
  | Expr.CellData c             -> Tll.CellData (cell_to_tll_cell c)
  | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarElem (variable_to_tll_var v)
  | Expr.ElemArrayRd _          -> raise(UnsupportedTllExpr(Expr.elem_to_str e))
  | Expr.HavocListElem          -> Tll.HavocListElem
  | Expr.HavocSkiplistElem      -> raise(UnsupportedTllExpr(Expr.elem_to_str e))
  | Expr.LowestElem             -> Tll.LowestElem
  | Expr.HighestElem            -> Tll.HighestElem


and addr_to_tll_addr (a:Expr.addr) : Tll.addr =
  match a with
    Expr.VarAddr v              -> Tll.VarAddr (variable_to_tll_var v)
  | Expr.Null                   -> Tll.Null
  | Expr.Next c                 -> Tll.Next (cell_to_tll_cell c)
  | Expr.NextAt _               -> raise(UnsupportedTllExpr(Expr.addr_to_str a))
  | Expr.FirstLocked (m,p)      -> Tll.FirstLocked (mem_to_tll_mem m,
                                                    path_to_tll_path p)
  | Expr.FirstLockedAt _        -> raise(UnsupportedTllExpr(Expr.addr_to_str a))
  | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarAddr (variable_to_tll_var v)
  | Expr.AddrArrayRd _          -> raise(UnsupportedTllExpr(Expr.addr_to_str a))
  | Expr.AddrArrRd _            -> raise(UnsupportedTllExpr(Expr.addr_to_str a))


and cell_to_tll_cell (c:Expr.cell) : Tll.cell =
  match c with
    Expr.VarCell v      -> Tll.VarCell (variable_to_tll_var v)
  | Expr.Error          -> Tll.Error
  | Expr.MkCell (e,a,t) -> Tll.MkCell (elem_to_tll_elem e,
                                       addr_to_tll_addr a,
                                       tid_to_tll_tid t)
  | Expr.MkSLKCell _    -> raise(UnsupportedTllExpr(Expr.cell_to_str c))
  | Expr.MkSLCell _     -> raise(UnsupportedTllExpr(Expr.cell_to_str c))
  (* Tll receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | Expr.CellLock c     -> Tll.CellLock (cell_to_tll_cell c, Tll.NoThid)
  | Expr.CellLockAt _   -> raise(UnsupportedTllExpr(Expr.cell_to_str c))
  | Expr.CellUnlock c   -> Tll.CellUnlock (cell_to_tll_cell c)
  | Expr.CellUnlockAt _ -> raise(UnsupportedTllExpr(Expr.cell_to_str c))
  | Expr.CellAt (m,a)   -> Tll.CellAt (mem_to_tll_mem m, addr_to_tll_addr a)
  | Expr.CellArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarCell (variable_to_tll_var v)
  | Expr.CellArrayRd _  -> raise(UnsupportedTllExpr(Expr.cell_to_str c))


and setth_to_tll_setth (st:Expr.setth) : Tll.setth =
  let to_setth = setth_to_tll_setth in
  match st with
    Expr.VarSetTh v        -> Tll.VarSetTh (variable_to_tll_var v)
  | Expr.EmptySetTh        -> Tll.EmptySetTh
  | Expr.SinglTh t         -> Tll.SinglTh (tid_to_tll_tid t)
  | Expr.UnionTh (s1,s2)   -> Tll.UnionTh (to_setth s1, to_setth s2)
  | Expr.IntrTh (s1,s2)    -> Tll.IntrTh (to_setth s1, to_setth s2)
  | Expr.SetdiffTh (s1,s2) -> Tll.SetdiffTh (to_setth s1, to_setth s2)
  | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarSetTh (variable_to_tll_var v)
  | Expr.SetThArrayRd _    -> raise(UnsupportedTllExpr
                                            (Expr.setth_to_str st))


and setelem_to_tll_setelem (st:Expr.setelem) : Tll.setelem =
  let to_setelem = setelem_to_tll_setelem in
  match st with
    Expr.VarSetElem v        -> Tll.VarSetElem (variable_to_tll_var v)
  | Expr.EmptySetElem        -> Tll.EmptySetElem
  | Expr.SinglElem e         -> Tll.SinglElem (elem_to_tll_elem e)
  | Expr.UnionElem (s1,s2)   -> Tll.UnionElem (to_setelem s1, to_setelem s2)
  | Expr.IntrElem (s1,s2)    -> Tll.IntrElem (to_setelem s1, to_setelem s2)
  | Expr.SetdiffElem (s1,s2) -> Tll.SetdiffElem (to_setelem s1, to_setelem s2)
  | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarSetElem (variable_to_tll_var v)
  | Expr.SetToElems (s,m)    -> Tll.SetToElems (set_to_tll_set s,
                                                mem_to_tll_mem m)
  | Expr.SetElemArrayRd _    -> raise(UnsupportedTllExpr
                                            (Expr.setelem_to_str st))


and path_to_tll_path (p:Expr.path) : Tll.path =
  match p with
    Expr.VarPath v         -> Tll.VarPath (variable_to_tll_var v)
  | Expr.Epsilon           -> Tll.Epsilon
  | Expr.SimplePath a      -> Tll.SimplePath (addr_to_tll_addr a)
  | Expr.GetPath (m,a1,a2) -> Tll.GetPath (mem_to_tll_mem m,
                                           addr_to_tll_addr a1,
                                           addr_to_tll_addr a2)
  | Expr.GetPathAt _       -> raise(UnsupportedTllExpr(Expr.path_to_str p))
  | Expr.PathArrayRd _     -> raise(UnsupportedTllExpr(Expr.path_to_str p))


and mem_to_tll_mem (m:Expr.mem) : Tll.mem =
  match m with
    Expr.VarMem v       -> Tll.VarMem (variable_to_tll_var v)
  | Expr.Update (m,a,c) -> Tll.Update (mem_to_tll_mem m,
                                       addr_to_tll_addr a,
                                       cell_to_tll_cell c)
  (* Missing the case for "emp" *)
  | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tll.VarMem (variable_to_tll_var v)
  | Expr.MemArrayRd _        -> raise (UnsupportedTllExpr (Expr.mem_to_str m))


and atom_to_tll_atom (a:Expr.atom) : Tll.atom =
  let path    = path_to_tll_path       in
  let mem     = mem_to_tll_mem         in
  let addr    = addr_to_tll_addr       in
  let elem    = elem_to_tll_elem       in
  let set     = set_to_tll_set         in
  let tid     = tid_to_tll_tid         in
  let setth   = setth_to_tll_setth     in
  let setelem = setelem_to_tll_setelem in
  let term    = term_to_tll_term       in
  match a with
    Expr.Append (p1,p2,p3)    -> Tll.Append (path p1,path p2,path p3)
  | Expr.Reach (m,a1,a2,p)    -> Tll.Reach (mem m, addr a1, addr a2, path p)
  | Expr.ReachAt _            -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.OrderList(m,a1,a2)   -> Tll.OrderList (mem m, addr a1, addr a2)
  | Expr.Skiplist _           -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.In (a,s)             -> Tll.In (addr a, set s)
  | Expr.SubsetEq (s1,s2)     -> Tll.SubsetEq (set s1, set s2)
  | Expr.InTh (t,s)           -> Tll.InTh (tid t, setth s)
  | Expr.SubsetEqTh (s1,s2)   -> Tll.SubsetEqTh (setth s1, setth s2)
  | Expr.InInt _              -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.SubsetEqInt _        -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.InElem (e,s)         -> Tll.InElem (elem_to_tll_elem e, setelem s)
  | Expr.SubsetEqElem (s1,s2) -> Tll.SubsetEqElem (setelem s1, setelem s2)
  | Expr.Less _               -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.Greater _            -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.LessEq _             -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.LessTid _            -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.LessElem (e1,e2)     -> Tll.LessElem (elem e1, elem e2)
  | Expr.GreaterElem (e1,e2)  -> Tll.GreaterElem (elem e1, elem e2)
  | Expr.GreaterEq _          -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.Eq (t1,t2)           -> Tll.Eq (term t1, term t2)
  | Expr.InEq (t1,t2)         -> Tll.InEq (term t1, term t2)
  | Expr.BoolVar _            -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.BoolArrayRd _        -> raise(UnsupportedTllExpr(Expr.atom_to_str a))
  | Expr.PC (pc,t,pr)         -> Tll.PC (pc, Option.lift tid_to_tll_tid t,pr)
  | Expr.PCUpdate (pc,t)      -> Tll.PCUpdate (pc, tid_to_tll_tid t)
  | Expr.PCRange (pc1,pc2,t,pr) -> Tll.PCRange (pc1, pc2,
                                        Option.lift tid_to_tll_tid t,pr)


and literal_to_tll_literal (l:Expr.literal) : Tll.literal =
  match l with
    Expr.Atom a    -> Tll.Atom (atom_to_tll_atom a)
  | Expr.NegAtom a -> Tll.NegAtom (atom_to_tll_atom a)


and formula_to_tll_formula (f:Expr.formula) : Tll.formula =
  let to_formula = formula_to_tll_formula in
  match f with
    Expr.Literal l       -> Tll.Literal (literal_to_tll_literal l)
  | Expr.True            -> Tll.True
  | Expr.False           -> Tll.False
  | Expr.And (f1,f2)     -> Tll.And (to_formula f1, to_formula f2)
  | Expr.Or (f1,f2)      -> Tll.Or (to_formula f1, to_formula f2)
  | Expr.Not f1          -> Tll.Not (to_formula f1)
  | Expr.Implies (f1,f2) -> Tll.Implies (to_formula f1, to_formula f2)
  | Expr.Iff (f1,f2)     -> Tll.Iff (to_formula f1, to_formula f2)
