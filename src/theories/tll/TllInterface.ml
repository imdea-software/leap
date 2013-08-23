open LeapLib

module E   = Expression
module TLL = TllExpression


type varId = E.varId
type sort  = E.sort
type tid   = E.tid

exception UnsupportedSort of string
exception UnsupportedTllExpr of string



(* Expression to TllExpression conversion *)


let rec sort_to_tll_sort (s:E.sort) : TLL.sort =
  match s with
  | E.Set       -> TLL.Set
  | E.Elem      -> TLL.Elem
  | E.Tid      -> TLL.Tid
  | E.Addr      -> TLL.Addr
  | E.Cell      -> TLL.Cell
  | E.SetTh     -> TLL.SetTh
  | E.SetInt    -> raise(UnsupportedSort(E.sort_to_str s))
  | E.SetElem   -> TLL.SetElem
  | E.Path      -> TLL.Path
  | E.Mem       -> TLL.Mem
  | E.Bool      -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Int       -> TLL.Int
  | E.Array     -> raise(UnsupportedSort(E.sort_to_str s))
  | E.AddrArray -> raise(UnsupportedSort(E.sort_to_str s))
  | E.TidArray  -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Unknown   -> TLL.Unknown


and sort_to_expr_sort (s:TLL.sort) : E.sort =
  match s with
  | TLL.Set     -> E.Set
  | TLL.Elem    -> E.Elem
  | TLL.Tid    -> E.Tid
  | TLL.Addr    -> E.Addr
  | TLL.Cell    -> E.Cell
  | TLL.SetTh   -> E.SetTh
  | TLL.SetElem -> E.SetElem
  | TLL.Path    -> E.Path
  | TLL.Mem     -> E.Mem
  | TLL.Int     -> E.Int
  | TLL.Bool    -> E.Bool
  | TLL.Unknown -> E.Unknown


and build_term_var (v:E.variable) : TLL.term =
  let tll_v = variable_to_tll_var v in
  match (E.var_sort v) with
    E.Set   -> TLL.SetT   (TLL.VarSet   tll_v)
  | E.Elem  -> TLL.ElemT  (TLL.VarElem  tll_v)
  | E.Tid  -> TLL.TidT  (TLL.VarTh    tll_v)
  | E.Addr  -> TLL.AddrT  (TLL.VarAddr  tll_v)
  | E.Cell  -> TLL.CellT  (TLL.VarCell  tll_v)
  | E.SetTh -> TLL.SetThT (TLL.VarSetTh tll_v)
  | E.Path  -> TLL.PathT  (TLL.VarPath  tll_v)
  | E.Int   -> TLL.IntT   (TLL.VarInt   tll_v)
  | E.Mem   -> TLL.MemT   (TLL.VarMem   tll_v)
  | _          -> TLL.VarT   (tll_v)



and variable_to_tll_var (v:E.variable) : TLL.variable =
  TLL.build_var (E.var_id v)
                (sort_to_tll_sort (E.var_sort v))
                (E.var_is_primed v)
                (shared_to_tll_shared (E.var_parameter v))
                (scope_to_tll_scope (E.var_scope v))


and shared_to_tll_shared (th:E.shared_or_local) : TLL.shared_or_local =
  match th with
  | E.Shared  -> TLL.Shared
  | E.Local t -> TLL.Local (tid_to_tll_tid t)


and scope_to_tll_scope (p:E.procedure_name) : TLL.procedure_name =
  match p with
  | E.GlobalScope -> TLL.GlobalScope
  | E.Scope proc  -> TLL.Scope proc


and tid_to_tll_tid (th:E.tid) : TLL.tid =
  match th with
    E.VarTh v        -> TLL.VarTh (variable_to_tll_var v)
  | E.NoTid         -> TLL.NoTid
  | E.CellLockId c   -> TLL.CellLockId (cell_to_tll_cell c)
  | E.CellLockIdAt _ -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.TidArrayRd _  -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.TidArrRd _    -> raise(UnsupportedTllExpr(E.tid_to_str th))


and term_to_tll_term (t:E.term) : TLL.term =
  match t with
    E.VarT v       -> TLL.VarT (variable_to_tll_var v)
  | E.SetT s       -> TLL.SetT (set_to_tll_set s)
  | E.ElemT e      -> TLL.ElemT (elem_to_tll_elem e)
  | E.TidT t      -> TLL.TidT (tid_to_tll_tid t)
  | E.AddrT a      -> TLL.AddrT (addr_to_tll_addr a)
  | E.CellT c      -> TLL.CellT (cell_to_tll_cell c)
  | E.SetThT st    -> TLL.SetThT (setth_to_tll_setth st)
  | E.SetIntT _    -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.SetElemT st  -> TLL.SetElemT (setelem_to_tll_setelem st)
  | E.PathT p      -> TLL.PathT (path_to_tll_path p)
  | E.MemT m       -> TLL.MemT (mem_to_tll_mem m)
  | E.IntT i       -> TLL.IntT (int_to_tll_int i)
  | E.AddrArrayT a -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.TidArrayT a  -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.ArrayT a     -> arrays_to_tll_term a


and arrays_to_tll_term (a:E.arrays) : TLL.term =
  match a with
  | E.VarArray v -> build_term_var v
  | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
      let tll_v  = variable_to_tll_var v in
      let tll_th = tid_to_tll_tid th_p in
      let tll_t  = term_to_tll_term t
      in
        TLL.VarUpdate (tll_v, tll_th, tll_t)
  | E.ArrayUp (_,_,e) -> raise(UnsupportedTllExpr(E.expr_to_str e))


and eq_to_tll_eq ((t1,t2):E.eq) : TLL.eq =
  (term_to_tll_term t1, term_to_tll_term t2)


and diseq_to_tll_eq ((t1,t2):E.diseq) : TLL.diseq =
  (term_to_tll_term t1, term_to_tll_term t2)


and set_to_tll_set (s:E.set) : TLL.set =
  let to_set = set_to_tll_set in
  match s with
    E.VarSet v        -> TLL.VarSet (variable_to_tll_var v)
  | E.EmptySet        -> TLL.EmptySet
  | E.Singl a         -> TLL.Singl (addr_to_tll_addr a)
  | E.Union (s1,s2)   -> TLL.Union (to_set s1, to_set s2)
  | E.Intr (s1,s2)    -> TLL.Intr (to_set s1, to_set s2)
  | E.Setdiff (s1,s2) -> TLL.Setdiff (to_set s1, to_set s2)
  | E.PathToSet p     -> TLL.PathToSet (path_to_tll_path p)
  | E.AddrToSet (m,a) -> TLL.AddrToSet (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.AddrToSetAt _   -> raise(UnsupportedTllExpr(E.set_to_str s))
  | E.SetArrayRd (E.VarArray v,t) ->
      TLL.VarSet (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.SetArrayRd _          -> raise(UnsupportedTllExpr(E.set_to_str s))


and elem_to_tll_elem (e:E.elem) : TLL.elem =
  match e with
    E.VarElem v              -> TLL.VarElem (variable_to_tll_var v)
  | E.CellData c             -> TLL.CellData (cell_to_tll_cell c)
  | E.ElemArrayRd (E.VarArray v,t) ->
      TLL.VarElem (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.ElemArrayRd _          -> raise(UnsupportedTllExpr(E.elem_to_str e))
  | E.HavocListElem          -> TLL.HavocListElem
  | E.HavocSkiplistElem      -> raise(UnsupportedTllExpr(E.elem_to_str e))
  | E.LowestElem             -> TLL.LowestElem
  | E.HighestElem            -> TLL.HighestElem


and addr_to_tll_addr (a:E.addr) : TLL.addr =
  match a with
    E.VarAddr v              -> TLL.VarAddr (variable_to_tll_var v)
  | E.Null                   -> TLL.Null
  | E.Next c                 -> TLL.Next (cell_to_tll_cell c)
  | E.NextAt _               -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.ArrAt _                -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.FirstLocked (m,p)      -> TLL.FirstLocked (mem_to_tll_mem m,
                                                    path_to_tll_path p)
  | E.FirstLockedAt _        -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.AddrArrayRd (E.VarArray v,t) ->
      TLL.VarAddr (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.AddrArrayRd _          -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.AddrArrRd _            -> raise(UnsupportedTllExpr(E.addr_to_str a))


and cell_to_tll_cell (c:E.cell) : TLL.cell =
  match c with
    E.VarCell v      -> TLL.VarCell (variable_to_tll_var v)
  | E.Error          -> TLL.Error
  | E.MkCell (e,a,t) -> TLL.MkCell (elem_to_tll_elem e,
                                       addr_to_tll_addr a,
                                       tid_to_tll_tid t)
  | E.MkSLKCell _    -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.MkSLCell _     -> raise(UnsupportedTllExpr(E.cell_to_str c))
  (* Tll receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | E.CellLock (c,t) -> TLL.CellLock (cell_to_tll_cell c, tid_to_tll_tid t)
  | E.CellLockAt _   -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.CellUnlock c   -> TLL.CellUnlock (cell_to_tll_cell c)
  | E.CellUnlockAt _ -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.CellAt (m,a)   -> TLL.CellAt (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.CellArrayRd (E.VarArray v,t) ->
      TLL.VarCell (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.CellArrayRd _  -> raise(UnsupportedTllExpr(E.cell_to_str c))


and setth_to_tll_setth (st:E.setth) : TLL.setth =
  let to_setth = setth_to_tll_setth in
  match st with
    E.VarSetTh v        -> TLL.VarSetTh (variable_to_tll_var v)
  | E.EmptySetTh        -> TLL.EmptySetTh
  | E.SinglTh t         -> TLL.SinglTh (tid_to_tll_tid t)
  | E.UnionTh (s1,s2)   -> TLL.UnionTh (to_setth s1, to_setth s2)
  | E.IntrTh (s1,s2)    -> TLL.IntrTh (to_setth s1, to_setth s2)
  | E.SetdiffTh (s1,s2) -> TLL.SetdiffTh (to_setth s1, to_setth s2)
  | E.SetThArrayRd (E.VarArray v,t) ->
      TLL.VarSetTh (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.SetThArrayRd _    -> raise(UnsupportedTllExpr(E.setth_to_str st))


and setelem_to_tll_setelem (st:E.setelem) : TLL.setelem =
  let to_setelem = setelem_to_tll_setelem in
  match st with
    E.VarSetElem v        -> TLL.VarSetElem (variable_to_tll_var v)
  | E.EmptySetElem        -> TLL.EmptySetElem
  | E.SinglElem e         -> TLL.SinglElem (elem_to_tll_elem e)
  | E.UnionElem (s1,s2)   -> TLL.UnionElem (to_setelem s1, to_setelem s2)
  | E.IntrElem (s1,s2)    -> TLL.IntrElem (to_setelem s1, to_setelem s2)
  | E.SetdiffElem (s1,s2) -> TLL.SetdiffElem (to_setelem s1, to_setelem s2)
  | E.SetElemArrayRd (E.VarArray v,t) ->
      TLL.VarSetElem (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.SetToElems (s,m)    -> TLL.SetToElems (set_to_tll_set s,
                                                mem_to_tll_mem m)
  | E.SetElemArrayRd _    -> raise(UnsupportedTllExpr(E.setelem_to_str st))


and path_to_tll_path (p:E.path) : TLL.path =
  match p with
    E.VarPath v         -> TLL.VarPath (variable_to_tll_var v)
  | E.Epsilon           -> TLL.Epsilon
  | E.SimplePath a      -> TLL.SimplePath (addr_to_tll_addr a)
  | E.GetPath (m,a1,a2) -> TLL.GetPath (mem_to_tll_mem m,
                                           addr_to_tll_addr a1,
                                           addr_to_tll_addr a2)
  | E.GetPathAt _       -> raise(UnsupportedTllExpr(E.path_to_str p))
  | E.PathArrayRd _     -> raise(UnsupportedTllExpr(E.path_to_str p))


and mem_to_tll_mem (m:E.mem) : TLL.mem =
  match m with
    E.VarMem v       -> TLL.VarMem (variable_to_tll_var v)
  | E.Update (m,a,c) -> TLL.Update (mem_to_tll_mem m,
                                       addr_to_tll_addr a,
                                       cell_to_tll_cell c)
  (* Missing the case for "emp" *)
  | E.MemArrayRd (E.VarArray v,t) ->
      TLL.VarMem (variable_to_tll_var (E.var_set_param (E.Local t) v))
  | E.MemArrayRd _        -> raise(UnsupportedTllExpr(E.mem_to_str m))


and int_to_tll_int (i:E.integer) : TLL.integer =
  match i with
    E.IntVal n -> TLL.IntVal n
  | E.VarInt v -> TLL.VarInt (variable_to_tll_var v)
  | E.IntNeg j -> TLL.IntNeg (int_to_tll_int j)
  | E.IntAdd (j1,j2) -> TLL.IntAdd (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntSub (j1,j2) -> TLL.IntSub (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntMul (j1,j2) -> TLL.IntMul (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntDiv (j1,j2) -> TLL.IntDiv (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntArrayRd _   -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.IntSetMin _    -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.IntSetMax _    -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.CellMax _      -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.HavocLevel     -> raise(UnsupportedTllExpr(E.integer_to_str i))


and atom_to_tll_atom (a:E.atom) : TLL.atom =
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
    E.Append (p1,p2,p3)    -> TLL.Append (path p1,path p2,path p3)
  | E.Reach (m,a1,a2,p)    -> TLL.Reach (mem m, addr a1, addr a2, path p)
  | E.ReachAt _            -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.OrderList(m,a1,a2)   -> TLL.OrderList (mem m, addr a1, addr a2)
  | E.Skiplist _           -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.In (a,s)             -> TLL.In (addr a, set s)
  | E.SubsetEq (s1,s2)     -> TLL.SubsetEq (set s1, set s2)
  | E.InTh (t,s)           -> TLL.InTh (tid t, setth s)
  | E.SubsetEqTh (s1,s2)   -> TLL.SubsetEqTh (setth s1, setth s2)
  | E.InInt _              -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.SubsetEqInt _        -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.InElem (e,s)         -> TLL.InElem (elem_to_tll_elem e, setelem s)
  | E.SubsetEqElem (s1,s2) -> TLL.SubsetEqElem (setelem s1, setelem s2)
  | E.Less (i1,i2)         -> TLL.Less (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessEq (i1,i2)       -> TLL.LessEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.Greater (i1,i2)      -> TLL.Greater (int_to_tll_int i1, int_to_tll_int i2)
  | E.GreaterEq (i1,i2)    -> TLL.GreaterEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessTid _            -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.LessElem (e1,e2)     -> TLL.LessElem (elem e1, elem e2)
  | E.GreaterElem (e1,e2)  -> TLL.GreaterElem (elem e1, elem e2)
  | E.Eq (t1,t2)           -> TLL.Eq (term t1, term t2)
  | E.InEq (t1,t2)         -> TLL.InEq (term t1, term t2)
  | E.BoolVar v            -> TLL.BoolVar (variable_to_tll_var v)
  | E.BoolArrayRd _        -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.PC (pc,t,pr)         -> TLL.PC (pc, shared_to_tll_shared t, pr)  | 
  E.PCUpdate (pc,t)      -> TLL.PCUpdate (pc, tid_to_tll_tid t)
  | E.PCRange (pc1,pc2,t,pr) -> TLL.PCRange (pc1, pc2, shared_to_tll_shared t, pr)


and literal_to_tll_literal (l:E.literal) : TLL.literal =
  match l with
    E.Atom a    -> TLL.Atom (atom_to_tll_atom a)
  | E.NegAtom a -> TLL.NegAtom (atom_to_tll_atom a)


and formula_to_tll_formula (f:E.formula) : TLL.formula =
  let to_formula = formula_to_tll_formula in
  match f with
    E.Literal l       -> TLL.Literal (literal_to_tll_literal l)
  | E.True            -> TLL.True
  | E.False           -> TLL.False
  | E.And (f1,f2)     -> TLL.And (to_formula f1, to_formula f2)
  | E.Or (f1,f2)      -> TLL.Or (to_formula f1, to_formula f2)
  | E.Not f1          -> TLL.Not (to_formula f1)
  | E.Implies (f1,f2) -> TLL.Implies (to_formula f1, to_formula f2)
  | E.Iff (f1,f2)     -> TLL.Iff (to_formula f1, to_formula f2)
