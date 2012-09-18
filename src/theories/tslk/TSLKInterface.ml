open LeapLib

module Expr=Expression
module Tslk=TSLKExpression


type varId = Expr.varId
type sort  = Expr.sort
type tid   = Expr.tid

exception UnsupportedSort of string
exception UnsupportedTslkExpr of string



(* Expression to TslkExpression conversion *)


let rec sort_to_tslk_sort (s:Expr.sort) : Tslk.sort =
  match s with
    Expr.Set       -> Tslk.Set
  | Expr.Elem      -> Tslk.Elem
  | Expr.Thid      -> Tslk.Thid
  | Expr.Addr      -> Tslk.Addr
  | Expr.Cell      -> Tslk.Cell
  | Expr.SetTh     -> Tslk.SetTh
  | Expr.SetInt    -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.SetElem   -> Tslk.SetElem
  | Expr.Path      -> Tslk.Path
  | Expr.Mem       -> Tslk.Mem
  | Expr.Bool      -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Int       -> Tslk.Int
  | Expr.Array     -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.AddrArray -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.TidArray  -> raise (UnsupportedSort (Expr.sort_to_str s))
  | Expr.Unknown   -> Tslk.Unknown



and build_term_var (v:Expr.variable) : Tslk.term =
  let tslk_v = variable_to_tslk_var v in
  match Expr.var_sort v with
    Expr.Set       -> Tslk.SetT       (Tslk.VarSet        tslk_v)
  | Expr.Elem      -> Tslk.ElemT      (Tslk.VarElem       tslk_v)
  | Expr.Thid      -> Tslk.ThidT      (Tslk.VarTh         tslk_v)
  | Expr.Addr      -> Tslk.AddrT      (Tslk.VarAddr       tslk_v)
  | Expr.Cell      -> Tslk.CellT      (Tslk.VarCell       tslk_v)
  | Expr.SetTh     -> Tslk.SetThT     (Tslk.VarSetTh      tslk_v)
  | Expr.Path      -> Tslk.PathT      (Tslk.VarPath       tslk_v)
  | Expr.Mem       -> Tslk.MemT       (Tslk.VarMem        tslk_v)
  | Expr.Int       -> Tslk.IntT       (Tslk.VarInt        tslk_v)
  | _              -> Tslk.VarT       (tslk_v)



and variable_to_tslk_var (v:Expr.variable) : Tslk.variable =
  let (id,s,pr,th,p,_) = v
  in
    (id, sort_to_tslk_sort s, pr, Option.lift tid_to_tslk_tid th, p)



and tid_to_tslk_tid (th:Expr.tid) : Tslk.tid =
  match th with
    Expr.VarTh v            -> Tslk.VarTh (variable_to_tslk_var v)
  | Expr.NoThid             -> Tslk.NoThid
  | Expr.CellLockId _       -> raise (UnsupportedTslkExpr(Expr.tid_to_str th))
  | Expr.CellLockIdAt (c,l) -> Tslk.CellLockIdAt (cell_to_tslk_cell c,
                                                 int_to_tslk_int l)
  | Expr.ThidArrayRd _      -> raise (UnsupportedTslkExpr(Expr.tid_to_str th))
  | Expr.ThidArrRd (tt,i)   -> raise (UnsupportedTslkExpr(Expr.tid_to_str th))

and term_to_tslk_term (t:Expr.term) : Tslk.term =
  match t with
    Expr.VarT v        -> Tslk.VarT (variable_to_tslk_var v)
  | Expr.SetT s        -> Tslk.SetT (set_to_tslk_set s)
  | Expr.ElemT e       -> Tslk.ElemT (elem_to_tslk_elem e)
  | Expr.ThidT t       -> Tslk.ThidT (tid_to_tslk_tid t)
  | Expr.AddrT a       -> Tslk.AddrT (addr_to_tslk_addr a)
  | Expr.CellT c       -> Tslk.CellT (cell_to_tslk_cell c)
  | Expr.SetThT st     -> Tslk.SetThT (setth_to_tslk_setth st)
  | Expr.SetIntT _     -> raise(UnsupportedTslkExpr(Expr.term_to_str t))
  | Expr.SetElemT st   -> Tslk.SetElemT (setelem_to_tslk_setelem st)
  | Expr.PathT p       -> Tslk.PathT (path_to_tslk_path p)
  | Expr.MemT m        -> Tslk.MemT (mem_to_tslk_mem m)
  | Expr.IntT i        -> Tslk.IntT (int_to_tslk_int i)
  | Expr.AddrArrayT aa -> raise(UnsupportedTslkExpr(Expr.term_to_str t))
  | Expr.TidArrayT tt  -> raise(UnsupportedTslkExpr(Expr.term_to_str t))
  | Expr.ArrayT a      -> arrays_to_tslk_term a 


and arrays_to_tslk_term (a:Expr.arrays) : Tslk.term =
  match a with
    Expr.VarArray v -> build_term_var v
  | Expr.ArrayUp (Expr.VarArray v,th_p,Expr.Term t) ->
      let tslk_v  = variable_to_tslk_var v in
      let tslk_th = tid_to_tslk_tid th_p in
      let tslk_t  = term_to_tslk_term t
      in
        Tslk.VarUpdate (tslk_v, tslk_th, tslk_t)
  | Expr.ArrayUp (_,_,e) -> raise(UnsupportedTslkExpr(Expr.expr_to_str e))



and eq_to_tslk_eq ((t1,t2):Expr.eq) : Tslk.eq =
  (term_to_tslk_term t1, term_to_tslk_term t2)


and diseq_to_tslk_eq ((t1,t2):Expr.diseq) : Tslk.diseq =
  (term_to_tslk_term t1, term_to_tslk_term t2)


and set_to_tslk_set (s:Expr.set) : Tslk.set =
  let to_set = set_to_tslk_set in
  match s with
    Expr.VarSet v        -> Tslk.VarSet (variable_to_tslk_var v)
  | Expr.EmptySet        -> Tslk.EmptySet
  | Expr.Singl a         -> Tslk.Singl (addr_to_tslk_addr a)
  | Expr.Union (s1,s2)   -> Tslk.Union (to_set s1, to_set s2)
  | Expr.Intr (s1,s2)    -> Tslk.Intr (to_set s1, to_set s2)
  | Expr.Setdiff (s1,s2) -> Tslk.Setdiff (to_set s1, to_set s2)
  | Expr.PathToSet p     -> Tslk.PathToSet (path_to_tslk_path p)
  | Expr.AddrToSet (m,a) -> Tslk.AddrToSet (mem_to_tslk_mem m, addr_to_tslk_addr a)
  | Expr.SetArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarSet (variable_to_tslk_var v)
  | Expr.SetArrayRd _          -> raise (UnsupportedTslkExpr (Expr.set_to_str s))


and elem_to_tslk_elem (e:Expr.elem) : Tslk.elem =
  match e with
    Expr.VarElem v              -> Tslk.VarElem (variable_to_tslk_var v)
  | Expr.CellData c             -> Tslk.CellData (cell_to_tslk_cell c)
  | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarElem (variable_to_tslk_var v)
  | Expr.ElemArrayRd _          -> raise(UnsupportedTslkExpr(Expr.elem_to_str e))
  | Expr.HavocListElem          -> raise(UnsupportedTslkExpr(Expr.elem_to_str e))
  | Expr.HavocSkiplistElem      -> Tslk.HavocSkiplistElem
  | Expr.LowestElem             -> Tslk.LowestElem
  | Expr.HighestElem            -> Tslk.HighestElem


and addr_to_tslk_addr (a:Expr.addr) : Tslk.addr =
  match a with
    Expr.VarAddr v              -> Tslk.VarAddr (variable_to_tslk_var v)
  | Expr.Null                   -> Tslk.Null
  | Expr.Next _                 -> raise(UnsupportedTslkExpr(Expr.addr_to_str a))
  | Expr.NextAt (c,l)           -> Tslk.NextAt (cell_to_tslk_cell c, int_to_tslk_int l)
  | Expr.FirstLocked (m,p)      -> Tslk.FirstLocked (mem_to_tslk_mem m,
                                                    path_to_tslk_path p)
  | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarAddr (variable_to_tslk_var v)
  | Expr.AddrArrayRd _          -> raise(UnsupportedTslkExpr(Expr.addr_to_str a))
  | Expr.AddrArrRd (aa,i)       -> raise(UnsupportedTslkExpr(Expr.addr_to_str a))


and cell_to_tslk_cell (c:Expr.cell) : Tslk.cell =
  match c with
    Expr.VarCell v            -> Tslk.VarCell (variable_to_tslk_var v)
  | Expr.Error                -> Tslk.Error
  | Expr.MkCell _             -> raise(UnsupportedTslkExpr(Expr.cell_to_str c))
  | Expr.MkSLKCell (e,aa,tt,l)-> Tslk.MkCell (elem_to_tslk_elem e,
                                              List.map addr_to_tslk_addr aa,
                                              List.map tid_to_tslk_tid tt,
                                              int_to_tslk_int l)
  | Expr.MkSLCell (e,aa,tt,l) -> raise(UnsupportedTslkExpr(Expr.cell_to_str c))
  (* Tslk receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | Expr.CellLock _           -> raise(UnsupportedTslkExpr(Expr.cell_to_str c))
  | Expr.CellLockAt (c,l)     -> Tslk.CellLockAt (cell_to_tslk_cell c,
                                                 int_to_tslk_int l,
                                                 Tslk.NoThid)
  | Expr.CellUnlock _         -> raise(UnsupportedTslkExpr(Expr.cell_to_str c))
  | Expr.CellUnlockAt (c,l)   -> Tslk.CellUnlockAt (cell_to_tslk_cell c,
                                                   int_to_tslk_int l)
  | Expr.CellAt (m,a)         -> Tslk.CellAt (mem_to_tslk_mem m, addr_to_tslk_addr a)
  | Expr.CellArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarCell (variable_to_tslk_var v)
  | Expr.CellArrayRd _        -> raise(UnsupportedTslkExpr(Expr.cell_to_str c))


and setth_to_tslk_setth (st:Expr.setth) : Tslk.setth =
  let to_setth = setth_to_tslk_setth in
  match st with
    Expr.VarSetTh v        -> Tslk.VarSetTh (variable_to_tslk_var v)
  | Expr.EmptySetTh        -> Tslk.EmptySetTh
  | Expr.SinglTh t         -> Tslk.SinglTh (tid_to_tslk_tid t)
  | Expr.UnionTh (s1,s2)   -> Tslk.UnionTh (to_setth s1, to_setth s2)
  | Expr.IntrTh (s1,s2)    -> Tslk.IntrTh (to_setth s1, to_setth s2)
  | Expr.SetdiffTh (s1,s2) -> Tslk.SetdiffTh (to_setth s1, to_setth s2)
  | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarSetTh (variable_to_tslk_var v)
  | Expr.SetThArrayRd _    -> raise(UnsupportedTslkExpr
                                            (Expr.setth_to_str st))


and setelem_to_tslk_setelem (st:Expr.setelem) : Tslk.setelem =
  let to_setelem = setelem_to_tslk_setelem in
  match st with
    Expr.VarSetElem v        -> Tslk.VarSetElem (variable_to_tslk_var v)
  | Expr.EmptySetElem        -> Tslk.EmptySetElem
  | Expr.SinglElem e         -> Tslk.SinglElem (elem_to_tslk_elem e)
  | Expr.UnionElem (s1,s2)   -> Tslk.UnionElem (to_setelem s1, to_setelem s2)
  | Expr.IntrElem (s1,s2)    -> Tslk.IntrElem (to_setelem s1, to_setelem s2)
  | Expr.SetdiffElem (s1,s2) -> Tslk.SetdiffElem (to_setelem s1, to_setelem s2)
  | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarSetElem (variable_to_tslk_var v)
  | Expr.SetToElems (s,m)    -> Tslk.SetToElems (set_to_tslk_set s,
                                                mem_to_tslk_mem m)
  | Expr.SetElemArrayRd _    -> raise(UnsupportedTslkExpr
                                            (Expr.setelem_to_str st))


and path_to_tslk_path (p:Expr.path) : Tslk.path =
  match p with
    Expr.VarPath v         -> Tslk.VarPath (variable_to_tslk_var v)
  | Expr.Epsilon           -> Tslk.Epsilon
  | Expr.SimplePath a      -> Tslk.SimplePath (addr_to_tslk_addr a)
  | Expr.GetPath (m,a1,a2) -> Tslk.GetPath (mem_to_tslk_mem m,
                                           addr_to_tslk_addr a1,
                                           addr_to_tslk_addr a2)
  | Expr.PathArrayRd _     -> raise(UnsupportedTslkExpr(Expr.path_to_str p))


and mem_to_tslk_mem (m:Expr.mem) : Tslk.mem =
  match m with
    Expr.VarMem v       -> Tslk.VarMem (variable_to_tslk_var v)
  | Expr.Update (m,a,c) -> Tslk.Update (mem_to_tslk_mem m,
                                       addr_to_tslk_addr a,
                                       cell_to_tslk_cell c)
  (* Missing the case for "emp" *)
  | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
      let v = Expr.build_var id s pr (Some t) p Expr.Normal in
      Tslk.VarMem (variable_to_tslk_var v)
  | Expr.MemArrayRd _        -> raise (UnsupportedTslkExpr (Expr.mem_to_str m))


and int_to_tslk_int (i:Expr.integer) : Tslk.integer =
  match i with
    Expr.IntVal i       -> Tslk.IntVal i
  | Expr.VarInt v       -> Tslk.VarInt (variable_to_tslk_var v)
  | Expr.IntNeg i       -> Tslk.IntNeg (int_to_tslk_int i)
  | Expr.IntAdd (i1,i2) -> Tslk.IntAdd (int_to_tslk_int i1, int_to_tslk_int i2)
  | Expr.IntSub (i1,i2) -> Tslk.IntSub (int_to_tslk_int i1, int_to_tslk_int i2)
  | Expr.IntMul (i1,i2) -> Tslk.IntMul (int_to_tslk_int i1, int_to_tslk_int i2)
  | Expr.IntDiv (i1,i2) -> Tslk.IntDiv (int_to_tslk_int i1, int_to_tslk_int i2)
  | Expr.IntArrayRd _   -> raise(UnsupportedTslkExpr(Expr.integer_to_str i))
  | Expr.IntSetMin _    -> raise(UnsupportedTslkExpr(Expr.integer_to_str i))
  | Expr.IntSetMax _    -> raise(UnsupportedTslkExpr(Expr.integer_to_str i))
  | Expr.HavocLevel     -> Tslk.HavocLevel


and atom_to_tslk_atom (a:Expr.atom) : Tslk.atom =
  let path    = path_to_tslk_path       in
  let mem     = mem_to_tslk_mem         in
  let addr    = addr_to_tslk_addr       in
  let elem    = elem_to_tslk_elem       in
  let set     = set_to_tslk_set         in
  let tid     = tid_to_tslk_tid         in
  let setth   = setth_to_tslk_setth     in
  let setelem = setelem_to_tslk_setelem in
  let integ   = int_to_tslk_int         in
  let term    = term_to_tslk_term       in
  match a with
    Expr.Append (p1,p2,p3)    -> Tslk.Append (path p1,path p2,path p3)
  | Expr.Reach (m,a1,a2,p)    -> Tslk.Reach (mem m, addr a1, addr a2, path p)
  | Expr.OrderList(m,a1,a2)   -> Tslk.OrderList (mem m, addr a1, addr a2)
  | Expr.In (a,s)             -> Tslk.In (addr a, set s)
  | Expr.SubsetEq (s1,s2)     -> Tslk.SubsetEq (set s1, set s2)
  | Expr.InTh (t,s)           -> Tslk.InTh (tid t, setth s)
  | Expr.SubsetEqTh (s1,s2)   -> Tslk.SubsetEqTh (setth s1, setth s2)
  | Expr.InInt _              -> raise (UnsupportedTslkExpr(Expr.atom_to_str a))
  | Expr.SubsetEqInt _        -> raise (UnsupportedTslkExpr(Expr.atom_to_str a))
  | Expr.InElem (e,s)         -> Tslk.InElem (elem_to_tslk_elem e, setelem s)
  | Expr.SubsetEqElem (s1,s2) -> Tslk.SubsetEqElem (setelem s1, setelem s2)
  | Expr.Less (i1,i2)         -> Tslk.Less (integ i1, integ i2)
  | Expr.Greater (i1,i2)      -> Tslk.Greater (integ i1, integ i2)
  | Expr.LessEq (i1,i2)       -> Tslk.LessEq (integ i1, integ i2)
  | Expr.GreaterEq (i1,i2)    -> Tslk.GreaterEq (integ i1, integ i2)
  | Expr.LessTid _            -> raise (UnsupportedTslkExpr(Expr.atom_to_str a))
  | Expr.LessElem (e1,e2)     -> Tslk.LessElem (elem e1, elem e2)
  | Expr.GreaterElem (e1,e2)  -> Tslk.GreaterElem (elem e1, elem e2)
  | Expr.Eq (t1,t2)           -> Tslk.Eq (term t1, term t2)
  | Expr.InEq (t1,t2)         -> Tslk.InEq (term t1, term t2)
  | Expr.BoolVar _            -> raise (UnsupportedTslkExpr(Expr.atom_to_str a))
  | Expr.BoolArrayRd _        -> raise (UnsupportedTslkExpr(Expr.atom_to_str a))
  | Expr.PC (pc,t,pr)         -> Tslk.PC (pc, Option.lift tid_to_tslk_tid t,pr)
  | Expr.PCUpdate (pc,t)      -> Tslk.PCUpdate (pc, tid_to_tslk_tid t)
  | Expr.PCRange (pc1,pc2,t,pr) -> Tslk.PCRange (pc1, pc2,
                                        Option.lift tid_to_tslk_tid t,pr)


and literal_to_tslk_literal (l:Expr.literal) : Tslk.literal =
  match l with
    Expr.Atom a    -> Tslk.Atom (atom_to_tslk_atom a)
  | Expr.NegAtom a -> Tslk.NegAtom (atom_to_tslk_atom a)


and formula_to_tslk_formula (f:Expr.formula) : Tslk.formula =
  let to_formula = formula_to_tslk_formula in
  match f with
    Expr.Literal l       -> Tslk.Literal (literal_to_tslk_literal l)
  | Expr.True            -> Tslk.True
  | Expr.False           -> Tslk.False
  | Expr.And (f1,f2)     -> Tslk.And (to_formula f1, to_formula f2)
  | Expr.Or (f1,f2)      -> Tslk.Or (to_formula f1, to_formula f2)
  | Expr.Not f1          -> Tslk.Not (to_formula f1)
  | Expr.Implies (f1,f2) -> Tslk.Implies (to_formula f1, to_formula f2)
  | Expr.Iff (f1,f2)     -> Tslk.Iff (to_formula f1, to_formula f2)
