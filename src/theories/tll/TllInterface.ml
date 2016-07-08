
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)



module E   = Expression
module TLL = TllExpression

exception UnsupportedSort of string
exception UnsupportedTllExpr of string
exception UnsupportedExpr of string



(* Expression to TllExpression conversion *)


let rec sort_to_tll_sort (s:E.sort) : TLL.sort =
  match s with
  | E.Set         -> TLL.Set
  | E.Elem        -> TLL.Elem
  | E.Tid         -> TLL.Tid
  | E.Addr        -> TLL.Addr
  | E.Cell        -> TLL.Cell
  | E.SetTh       -> TLL.SetTh
  | E.SetInt      -> raise(UnsupportedSort(E.sort_to_str s))
  | E.SetElem     -> TLL.SetElem
  | E.SetPair     -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Path        -> TLL.Path
  | E.Mem         -> TLL.Mem
  | E.Bool        -> TLL.Bool
  | E.Int         -> TLL.Int
  | E.Pair        -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Array       -> raise(UnsupportedSort(E.sort_to_str s))
  | E.AddrArray   -> raise(UnsupportedSort(E.sort_to_str s))
  | E.TidArray    -> raise(UnsupportedSort(E.sort_to_str s))
  | E.BucketArray -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Mark        -> TLL.Mark
  | E.Bucket      -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Lock        -> raise(UnsupportedSort(E.sort_to_str s))
  | E.LockArray   -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Unknown     -> TLL.Unknown


and build_term_var (v:E.V.t) : TLL.term =
  let tll_v = var_to_tll_var v in
  match (E.V.sort v) with
    E.Set     -> TLL.SetT     (TLL.VarSet     tll_v)
  | E.Elem    -> TLL.ElemT    (TLL.VarElem    tll_v)
  | E.Tid     -> TLL.TidT     (TLL.VarTh      tll_v)
  | E.Addr    -> TLL.AddrT    (TLL.VarAddr    tll_v)
  | E.Cell    -> TLL.CellT    (TLL.VarCell    tll_v)
  | E.SetTh   -> TLL.SetThT   (TLL.VarSetTh   tll_v)
  | E.SetElem -> TLL.SetElemT (TLL.VarSetElem tll_v)
  | E.Path    -> TLL.PathT    (TLL.VarPath    tll_v)
  | E.Int     -> TLL.IntT     (TLL.VarInt     tll_v)
  | E.Mem     -> TLL.MemT     (TLL.VarMem     tll_v)
  | E.Mark    -> TLL.MarkT    (TLL.VarMark    tll_v)
  | _         -> TLL.VarT     (tll_v)



and var_to_tll_var (v:E.V.t) : TLL.V.t =
  TLL.build_var (E.V.id v)
                (sort_to_tll_sort (E.V.sort v))
                (E.V.is_primed v)
                (shared_to_tll_shared (E.V.parameter v))
                (scope_to_tll_scope (E.V.scope v))
                 ~treat_as_pc:(E.is_pc_var v)


and shared_to_tll_shared (th:E.V.shared_or_local) : TLL.V.shared_or_local =
  match th with
  | E.V.Shared  -> TLL.V.Shared
  | E.V.Local t -> TLL.V.Local (var_to_tll_var t)


and scope_to_tll_scope (p:E.V.procedure_name) : TLL.V.procedure_name =
  match p with
  | E.V.GlobalScope -> TLL.V.GlobalScope
  | E.V.Scope proc  -> TLL.V.Scope proc


and tid_to_tll_tid (th:E.tid) : TLL.tid =
  match th with
    E.VarTh v        -> TLL.VarTh (var_to_tll_var v)
  | E.NoTid          -> TLL.NoTid
  | E.CellLockId c   -> TLL.CellLockId (cell_to_tll_cell c)
  | E.CellLockIdAt _ -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.TidArrayRd _   -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.TidArrRd _     -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.PairTid _      -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.BucketTid _    -> raise(UnsupportedTllExpr(E.tid_to_str th))
  | E.LockId _       -> raise(UnsupportedTllExpr(E.tid_to_str th))


and term_to_tll_term (t:E.term) : TLL.term =
  match t with
    E.VarT v          -> TLL.VarT (var_to_tll_var v)
  | E.SetT s          -> TLL.SetT (set_to_tll_set s)
  | E.ElemT e         -> TLL.ElemT (elem_to_tll_elem e)
  | E.TidT t          -> TLL.TidT (tid_to_tll_tid t)
  | E.AddrT a         -> TLL.AddrT (addr_to_tll_addr a)
  | E.CellT c         -> TLL.CellT (cell_to_tll_cell c)
  | E.SetThT st       -> TLL.SetThT (setth_to_tll_setth st)
  | E.SetIntT _       -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.SetElemT st     -> TLL.SetElemT (setelem_to_tll_setelem st)
  | E.SetPairT _      -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.PathT p         -> TLL.PathT (path_to_tll_path p)
  | E.MemT m          -> TLL.MemT (mem_to_tll_mem m)
  | E.IntT i          -> TLL.IntT (int_to_tll_int i)
  | E.PairT _         -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.AddrArrayT _    -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.TidArrayT _     -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.BucketArrayT _  -> (print_endline "Converting array!!!"; raise(UnsupportedTllExpr(E.term_to_str t)))
  | E.MarkT m         -> TLL.MarkT (mark_to_tll_mark m)
  | E.BucketT _       -> (print_endline "Converting bucket!!!"; raise(UnsupportedTllExpr(E.term_to_str t)))
  | E.LockT _         -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.LockArrayT _    -> raise(UnsupportedTllExpr(E.term_to_str t))
  | E.ArrayT a        -> arrays_to_tll_term a


and arrays_to_tll_term (a:E.arrays) : TLL.term =
  match a with
  | E.VarArray v -> build_term_var v
  | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
      let tll_v  = var_to_tll_var v in
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
    E.VarSet v        -> TLL.VarSet (var_to_tll_var v)
  | E.EmptySet        -> TLL.EmptySet
  | E.Singl a         -> TLL.Singl (addr_to_tll_addr a)
  | E.Union (s1,s2)   -> TLL.Union (to_set s1, to_set s2)
  | E.Intr (s1,s2)    -> TLL.Intr (to_set s1, to_set s2)
  | E.Setdiff (s1,s2) -> TLL.Setdiff (to_set s1, to_set s2)
  | E.PathToSet p     -> TLL.PathToSet (path_to_tll_path p)
  | E.AddrToSet (m,a) -> TLL.AddrToSet (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.AddrToSetAt _   -> raise(UnsupportedTllExpr(E.set_to_str s))
  | E.SetArrayRd (E.VarArray v,t) ->
      TLL.VarSet (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetArrayRd _    -> raise(UnsupportedTllExpr(E.set_to_str s))
  | E.BucketRegion _  -> raise(UnsupportedTllExpr(E.set_to_str s))


and elem_to_tll_elem (e:E.elem) : TLL.elem =
  match e with
    E.VarElem v              -> TLL.VarElem (var_to_tll_var v)
  | E.CellData c             -> TLL.CellData (cell_to_tll_cell c)
  | E.ElemArrayRd (E.VarArray v,t) ->
      TLL.VarElem (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.ElemArrayRd _          -> raise(UnsupportedTllExpr(E.elem_to_str e))
  | E.HavocListElem          -> TLL.HavocListElem
  | E.HavocSkiplistElem      -> raise(UnsupportedTllExpr(E.elem_to_str e))
  | E.LowestElem             -> TLL.LowestElem
  | E.HighestElem            -> TLL.HighestElem


and addr_to_tll_addr (a:E.addr) : TLL.addr =
  match a with
    E.VarAddr v              -> TLL.VarAddr (var_to_tll_var v)
  | E.Null                   -> TLL.Null
  | E.Next c                 -> TLL.Next (cell_to_tll_cell c)
  | E.NextAt _               -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.ArrAt _                -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.FirstLocked (m,p)      -> TLL.FirstLocked (mem_to_tll_mem m,
                                                    path_to_tll_path p)
  | E.FirstLockedAt _        -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.LastLocked (m,p)       -> TLL.LastLocked (mem_to_tll_mem m,
                                                path_to_tll_path p)
  | E.AddrArrayRd (E.VarArray v,t) ->
      TLL.VarAddr (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.AddrArrayRd _          -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.AddrArrRd _            -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.BucketInit _           -> raise(UnsupportedTllExpr(E.addr_to_str a))
  | E.BucketEnd _            -> raise(UnsupportedTllExpr(E.addr_to_str a))


and cell_to_tll_cell (c:E.cell) : TLL.cell =
  match c with
    E.VarCell v            -> TLL.VarCell (var_to_tll_var v)
  | E.Error                -> TLL.Error
  | E.MkCell (e,a,t)       -> TLL.MkCell (elem_to_tll_elem e,
                                          addr_to_tll_addr a,
                                          tid_to_tll_tid t)
  | E.MkCellMark (e,a,t,m) -> TLL.MkCellMark (elem_to_tll_elem e,
                                              addr_to_tll_addr a,
                                              tid_to_tll_tid t,
                                              mark_to_tll_mark m)
  | E.MkSLKCell _          -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.MkSLCell _           -> raise(UnsupportedTllExpr(E.cell_to_str c))
  (* Tll receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | E.CellLock (c,t)       -> TLL.CellLock (cell_to_tll_cell c, tid_to_tll_tid t)
  | E.CellLockAt _         -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.CellUnlock c         -> TLL.CellUnlock (cell_to_tll_cell c)
  | E.CellUnlockAt _       -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.CellAt (m,a)         -> TLL.CellAt (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.CellArrayRd (E.VarArray v,t) ->
      TLL.VarCell (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.CellArrayRd _        -> raise(UnsupportedTllExpr(E.cell_to_str c))
  | E.UpdCellAddr _        -> raise(UnsupportedTllExpr(E.cell_to_str c))


and mark_to_tll_mark (m:E.mark) : TLL.mark =
  match m with
    E.VarMark v -> TLL.VarMark (var_to_tll_var v)
  | E.MarkTrue  -> TLL.MarkTrue
  | E.MarkFalse -> TLL.MarkFalse
  | E.Marked c  -> TLL.Marked (cell_to_tll_cell c)


and setth_to_tll_setth (st:E.setth) : TLL.setth =
  let to_setth = setth_to_tll_setth in
  match st with
    E.VarSetTh v        -> TLL.VarSetTh (var_to_tll_var v)
  | E.EmptySetTh        -> TLL.EmptySetTh
  | E.SinglTh t         -> TLL.SinglTh (tid_to_tll_tid t)
  | E.UnionTh (s1,s2)   -> TLL.UnionTh (to_setth s1, to_setth s2)
  | E.IntrTh (s1,s2)    -> TLL.IntrTh (to_setth s1, to_setth s2)
  | E.SetdiffTh (s1,s2) -> TLL.SetdiffTh (to_setth s1, to_setth s2)
  | E.SetThArrayRd (E.VarArray v,t) ->
      TLL.VarSetTh (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetThArrayRd _    -> raise(UnsupportedTllExpr(E.setth_to_str st))
  | E.LockSet (m,p)     -> TLL.LockSet (mem_to_tll_mem m,
                                        path_to_tll_path p)


and setelem_to_tll_setelem (st:E.setelem) : TLL.setelem =
  let to_setelem = setelem_to_tll_setelem in
  match st with
    E.VarSetElem v        -> TLL.VarSetElem (var_to_tll_var v)
  | E.EmptySetElem        -> TLL.EmptySetElem
  | E.SinglElem e         -> TLL.SinglElem (elem_to_tll_elem e)
  | E.UnionElem (s1,s2)   -> TLL.UnionElem (to_setelem s1, to_setelem s2)
  | E.IntrElem (s1,s2)    -> TLL.IntrElem (to_setelem s1, to_setelem s2)
  | E.SetdiffElem (s1,s2) -> TLL.SetdiffElem (to_setelem s1, to_setelem s2)
  | E.SetElemArrayRd (E.VarArray v,t) ->
      TLL.VarSetElem (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetToElems (s,m)    -> TLL.SetToElems (set_to_tll_set s,
                                                mem_to_tll_mem m)
  | E.SetElemArrayRd _    -> raise(UnsupportedTllExpr(E.setelem_to_str st))


and path_to_tll_path (p:E.path) : TLL.path =
  match p with
    E.VarPath v         -> TLL.VarPath (var_to_tll_var v)
  | E.Epsilon           -> TLL.Epsilon
  | E.SimplePath a      -> TLL.SimplePath (addr_to_tll_addr a)
  | E.GetPath (m,a1,a2) -> TLL.GetPath (mem_to_tll_mem m,
                                           addr_to_tll_addr a1,
                                           addr_to_tll_addr a2)
  | E.GetPathAt _       -> raise(UnsupportedTllExpr(E.path_to_str p))
  | E.PathArrayRd _     -> raise(UnsupportedTllExpr(E.path_to_str p))


and mem_to_tll_mem (m:E.mem) : TLL.mem =
  match m with
    E.VarMem v       -> TLL.VarMem (var_to_tll_var v)
  | E.Update (m,a,c) -> TLL.Update (mem_to_tll_mem m,
                                       addr_to_tll_addr a,
                                       cell_to_tll_cell c)
  (* Missing the case for "emp" *)
  | E.MemArrayRd (E.VarArray v,t) ->
      TLL.VarMem (var_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.MemArrayRd _        -> raise(UnsupportedTllExpr(E.mem_to_str m))


and int_to_tll_int (i:E.integer) : TLL.integer =
  match i with
    E.IntVal n -> TLL.IntVal n
  | E.VarInt v -> TLL.VarInt (var_to_tll_var v)
  | E.IntNeg j -> TLL.IntNeg (int_to_tll_int j)
  | E.IntAdd (j1,j2) -> TLL.IntAdd (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntSub (j1,j2) -> TLL.IntSub (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntMul (j1,j2) -> TLL.IntMul (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntDiv (j1,j2) -> TLL.IntDiv (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntMod (j1,j2) -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.IntArrayRd _   -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.IntSetMin _    -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.IntSetMax _    -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.CellMax _      -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.HavocLevel     -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.HashCode _     -> raise(UnsupportedTllExpr(E.integer_to_str i))
  | E.PairInt _      -> raise(UnsupportedTllExpr(E.integer_to_str i))


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
  | E.Hashtbl _            -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.In (a,s)             -> TLL.In (addr a, set s)
  | E.SubsetEq (s1,s2)     -> TLL.SubsetEq (set s1, set s2)
  | E.InTh (t,s)           -> TLL.InTh (tid t, setth s)
  | E.SubsetEqTh (s1,s2)   -> TLL.SubsetEqTh (setth s1, setth s2)
  | E.InInt _              -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.SubsetEqInt _        -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.InElem (e,s)         -> TLL.InElem (elem_to_tll_elem e, setelem s)
  | E.SubsetEqElem (s1,s2) -> TLL.SubsetEqElem (setelem s1, setelem s2)
  | E.InPair _             -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.SubsetEqPair _       -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.InTidPair _          -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.InIntPair _          -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.Less (i1,i2)         -> TLL.Less (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessEq (i1,i2)       -> TLL.LessEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.Greater (i1,i2)      -> TLL.Greater (int_to_tll_int i1, int_to_tll_int i2)
  | E.GreaterEq (i1,i2)    -> TLL.GreaterEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessTid _            -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.LessElem (e1,e2)     -> TLL.LessElem (elem e1, elem e2)
  | E.GreaterElem (e1,e2)  -> TLL.GreaterElem (elem e1, elem e2)
  | E.Eq (t1,t2)           -> TLL.Eq (term t1, term t2)
  | E.InEq (t1,t2)         -> TLL.InEq (term t1, term t2)
  | E.UniqueInt _          -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.UniqueTid _          -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.BoolVar v            -> TLL.BoolVar (var_to_tll_var v)
  | E.BoolArrayRd _        -> raise(UnsupportedTllExpr(E.atom_to_str a))
  | E.PC (pc,t,pr)         -> TLL.PC (pc, shared_to_tll_shared t, pr)
  | E.PCUpdate (pc,t)      -> TLL.PCUpdate (pc, tid_to_tll_tid t)
  | E.PCRange (pc1,pc2,t,pr) -> TLL.PCRange (pc1, pc2, shared_to_tll_shared t, pr)

and formula_to_tll_formula (phi:E.formula) : TLL.formula =
  Formula.formula_conv atom_to_tll_atom phi





let rec sort_to_expr_sort (s:TLL.sort) : E.sort =
  match s with
  | TLL.Set     -> E.Set
  | TLL.Elem    -> E.Elem
  | TLL.Tid     -> E.Tid
  | TLL.Addr    -> E.Addr
  | TLL.Cell    -> E.Cell
  | TLL.SetTh   -> E.SetTh
  | TLL.SetElem -> E.SetElem
  | TLL.Path    -> E.Path
  | TLL.Mem     -> E.Mem
  | TLL.Int     -> E.Int
  | TLL.Bool    -> E.Bool
  | TLL.Mark    -> E.Mark
  | TLL.Unknown -> E.Unknown


and var_to_expr_var (v:TLL.V.t) : E.V.t =
  E.build_var (TLL.V.id v)
              (sort_to_expr_sort (TLL.V.sort v))
              (TLL.V.is_primed v)
              (shared_to_expr_shared (TLL.V.parameter v))
              (scope_to_expr_scope (TLL.V.scope v))
               ~nature:E.RealVar


and shared_to_expr_shared (th:TLL.V.shared_or_local) : E.V.shared_or_local =
  match th with
  | TLL.V.Shared  -> E.V.Shared
  | TLL.V.Local t -> E.V.Local (var_to_expr_var t)


and scope_to_expr_scope (p:TLL.V.procedure_name) : E.V.procedure_name =
  match p with
  | TLL.V.GlobalScope -> E.V.GlobalScope
  | TLL.V.Scope proc  -> E.V.Scope proc


and tid_to_expr_tid (th:TLL.tid) : E.tid =
  match th with
    TLL.VarTh v        -> E.VarTh (var_to_expr_var v)
  | TLL.NoTid          -> E.NoTid
  | TLL.CellLockId c   -> E.CellLockId (cell_to_expr_cell c)


and term_to_expr_term (t:TLL.term) : E.term =
  match t with
    TLL.VarT v          -> E.VarT (var_to_expr_var v)
  | TLL.SetT s          -> E.SetT (set_to_expr_set s)
  | TLL.ElemT e         -> E.ElemT (elem_to_expr_elem e)
  | TLL.TidT t          -> E.TidT (tid_to_expr_tid t)
  | TLL.AddrT a         -> E.AddrT (addr_to_expr_addr a)
  | TLL.CellT c         -> E.CellT (cell_to_expr_cell c)
  | TLL.SetThT st       -> E.SetThT (setth_to_expr_setth st)
  | TLL.SetElemT st     -> E.SetElemT (setelem_to_expr_setelem st)
  | TLL.PathT p         -> E.PathT (path_to_expr_path p)
  | TLL.MemT m          -> E.MemT (mem_to_expr_mem m)
  | TLL.IntT i          -> E.IntT (int_to_expr_int i)
  | TLL.MarkT m         -> E.MarkT (mark_to_expr_mark m)
  | TLL.VarUpdate (v,th,t) ->
      let expr_a  = E.VarArray (var_to_expr_var v) in
      let expr_th = tid_to_expr_tid th in
      let expr_t  = E.Term (term_to_expr_term t)
      in
        E.ArrayT (E.ArrayUp (expr_a, expr_th, expr_t))


and eq_to_expr_eq ((t1,t2):TLL.eq) : E.eq =
  (term_to_expr_term t1, term_to_expr_term t2)


and diseq_to_expr_eq ((t1,t2):TLL.diseq) : E.diseq =
  (term_to_expr_term t1, term_to_expr_term t2)


and set_to_expr_set (s:TLL.set) : E.set =
  let to_set = set_to_expr_set in
  match s with
    TLL.VarSet v        -> E.VarSet (var_to_expr_var v)
  | TLL.EmptySet        -> E.EmptySet
  | TLL.Singl a         -> E.Singl (addr_to_expr_addr a)
  | TLL.Union (s1,s2)   -> E.Union (to_set s1, to_set s2)
  | TLL.Intr (s1,s2)    -> E.Intr (to_set s1, to_set s2)
  | TLL.Setdiff (s1,s2) -> E.Setdiff (to_set s1, to_set s2)
  | TLL.PathToSet p     -> E.PathToSet (path_to_expr_path p)
  | TLL.AddrToSet (m,a) -> E.AddrToSet (mem_to_expr_mem m, addr_to_expr_addr a)


and elem_to_expr_elem (e:TLL.elem) : E.elem =
  match e with
    TLL.VarElem v              -> E.VarElem (var_to_expr_var v)
  | TLL.CellData c             -> E.CellData (cell_to_expr_cell c)
  | TLL.HavocListElem          -> E.HavocListElem
  | TLL.LowestElem             -> E.LowestElem
  | TLL.HighestElem            -> E.HighestElem


and addr_to_expr_addr (a:TLL.addr) : E.addr =
  match a with
    TLL.VarAddr v              -> E.VarAddr (var_to_expr_var v)
  | TLL.Null                   -> E.Null
  | TLL.Next c                 -> E.Next (cell_to_expr_cell c)
  | TLL.FirstLocked (m,p)      -> E.FirstLocked (mem_to_expr_mem m,
                                                    path_to_expr_path p)
  | TLL.LastLocked (m,p)       -> E.LastLocked (mem_to_expr_mem m,
                                                path_to_expr_path p)


and cell_to_expr_cell (c:TLL.cell) : E.cell =
  match c with
    TLL.VarCell v            -> E.VarCell (var_to_expr_var v)
  | TLL.Error                -> E.Error
  | TLL.MkCell (e,a,t)       -> E.MkCell (elem_to_expr_elem e,
                                          addr_to_expr_addr a,
                                          tid_to_expr_tid t)
  | TLL.MkCellMark (e,a,t,m) -> E.MkCellMark (elem_to_expr_elem e,
                                              addr_to_expr_addr a,
                                              tid_to_expr_tid t,
                                              mark_to_expr_mark m)
  (* Tll receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | TLL.CellLock (c,t)       -> E.CellLock (cell_to_expr_cell c, tid_to_expr_tid t)
  | TLL.CellUnlock c         -> E.CellUnlock (cell_to_expr_cell c)
  | TLL.CellAt (m,a)         -> E.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


and mark_to_expr_mark (m:TLL.mark) : E.mark =
  match m with
    TLL.VarMark v -> E.VarMark (var_to_expr_var v)
  | TLL.MarkTrue  -> E.MarkTrue
  | TLL.MarkFalse -> E.MarkFalse
  | TLL.Marked c  -> E.Marked (cell_to_expr_cell c)


and setth_to_expr_setth (st:TLL.setth) : E.setth =
  let to_setth = setth_to_expr_setth in
  match st with
    TLL.VarSetTh v        -> E.VarSetTh (var_to_expr_var v)
  | TLL.EmptySetTh        -> E.EmptySetTh
  | TLL.SinglTh t         -> E.SinglTh (tid_to_expr_tid t)
  | TLL.UnionTh (s1,s2)   -> E.UnionTh (to_setth s1, to_setth s2)
  | TLL.IntrTh (s1,s2)    -> E.IntrTh (to_setth s1, to_setth s2)
  | TLL.SetdiffTh (s1,s2) -> E.SetdiffTh (to_setth s1, to_setth s2)
  | TLL.LockSet (m,p)     -> E.LockSet (mem_to_expr_mem m,
                                        path_to_expr_path p)


and setelem_to_expr_setelem (st:TLL.setelem) : E.setelem =
  let to_setelem = setelem_to_expr_setelem in
  match st with
    TLL.VarSetElem v        -> E.VarSetElem (var_to_expr_var v)
  | TLL.EmptySetElem        -> E.EmptySetElem
  | TLL.SinglElem e         -> E.SinglElem (elem_to_expr_elem e)
  | TLL.UnionElem (s1,s2)   -> E.UnionElem (to_setelem s1, to_setelem s2)
  | TLL.IntrElem (s1,s2)    -> E.IntrElem (to_setelem s1, to_setelem s2)
  | TLL.SetdiffElem (s1,s2) -> E.SetdiffElem (to_setelem s1, to_setelem s2)
  | TLL.SetToElems (s,m)    -> E.SetToElems (set_to_expr_set s,
                                                mem_to_expr_mem m)


and path_to_expr_path (p:TLL.path) : E.path =
  match p with
    TLL.VarPath v         -> E.VarPath (var_to_expr_var v)
  | TLL.Epsilon           -> E.Epsilon
  | TLL.SimplePath a      -> E.SimplePath (addr_to_expr_addr a)
  | TLL.GetPath (m,a1,a2) -> E.GetPath (mem_to_expr_mem m,
                                           addr_to_expr_addr a1,
                                           addr_to_expr_addr a2)


and mem_to_expr_mem (m:TLL.mem) : E.mem =
  match m with
    TLL.VarMem v       -> E.VarMem (var_to_expr_var v)
  | TLL.Update (m,a,c) -> E.Update (mem_to_expr_mem m,
                                       addr_to_expr_addr a,
                                       cell_to_expr_cell c)
  | TLL.Emp            -> raise(UnsupportedExpr(TLL.mem_to_str m))
  (* Missing the case for "emp" *)


and int_to_expr_int (i:TLL.integer) : E.integer =
  match i with
    TLL.IntVal n -> E.IntVal n
  | TLL.VarInt v -> E.VarInt (var_to_expr_var v)
  | TLL.IntNeg j -> E.IntNeg (int_to_expr_int j)
  | TLL.IntAdd (j1,j2) -> E.IntAdd (int_to_expr_int j1, int_to_expr_int j2)
  | TLL.IntSub (j1,j2) -> E.IntSub (int_to_expr_int j1, int_to_expr_int j2)
  | TLL.IntMul (j1,j2) -> E.IntMul (int_to_expr_int j1, int_to_expr_int j2)
  | TLL.IntDiv (j1,j2) -> E.IntDiv (int_to_expr_int j1, int_to_expr_int j2)


and atom_to_expr_atom (a:TLL.atom) : E.atom =
  let path    = path_to_expr_path       in
  let mem     = mem_to_expr_mem         in
  let addr    = addr_to_expr_addr       in
  let elem    = elem_to_expr_elem       in
  let set     = set_to_expr_set         in
  let tid     = tid_to_expr_tid         in
  let setth   = setth_to_expr_setth     in
  let setelem = setelem_to_expr_setelem in
  let term    = term_to_expr_term       in
  match a with
    TLL.Append (p1,p2,p3)    -> E.Append (path p1,path p2,path p3)
  | TLL.Reach (m,a1,a2,p)    -> E.Reach (mem m, addr a1, addr a2, path p)
  | TLL.OrderList(m,a1,a2)   -> E.OrderList (mem m, addr a1, addr a2)
  | TLL.In (a,s)             -> E.In (addr a, set s)
  | TLL.SubsetEq (s1,s2)     -> E.SubsetEq (set s1, set s2)
  | TLL.InTh (t,s)           -> E.InTh (tid t, setth s)
  | TLL.SubsetEqTh (s1,s2)   -> E.SubsetEqTh (setth s1, setth s2)
  | TLL.InElem (e,s)         -> E.InElem (elem_to_expr_elem e, setelem s)
  | TLL.SubsetEqElem (s1,s2) -> E.SubsetEqElem (setelem s1, setelem s2)
  | TLL.Less (i1,i2)         -> E.Less (int_to_expr_int i1, int_to_expr_int i2)
  | TLL.LessEq (i1,i2)       -> E.LessEq (int_to_expr_int i1, int_to_expr_int i2)
  | TLL.Greater (i1,i2)      -> E.Greater (int_to_expr_int i1, int_to_expr_int i2)
  | TLL.GreaterEq (i1,i2)    -> E.GreaterEq (int_to_expr_int i1, int_to_expr_int i2)
  | TLL.LessElem (e1,e2)     -> E.LessElem (elem e1, elem e2)
  | TLL.GreaterElem (e1,e2)  -> E.GreaterElem (elem e1, elem e2)
  | TLL.Eq (t1,t2)           -> E.Eq (term t1, term t2)
  | TLL.InEq (t1,t2)         -> E.InEq (term t1, term t2)
  | TLL.BoolVar v            -> E.BoolVar (var_to_expr_var v)
  | TLL.PC (pc,t,pr)         -> E.PC (pc, shared_to_expr_shared t, pr)
  | TLL.PCUpdate (pc,t)      -> E.PCUpdate (pc, tid_to_expr_tid t)
  | TLL.PCRange (pc1,pc2,t,pr) -> E.PCRange (pc1, pc2, shared_to_expr_shared t, pr)

and formula_to_expr_formula (phi:TLL.formula) : E.formula =
  Formula.formula_conv atom_to_expr_atom phi

