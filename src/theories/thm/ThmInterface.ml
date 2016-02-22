
module E   = Expression
module THM = ThmExpression

exception UnsupportedSort of string
exception UnsupportedThmExpr of string



(* Expression to ThmExpression conversion *)
let rec sort_to_thm_sort (s:E.sort) : THM.sort =
  match s with
  | E.Set         -> THM.Set
  | E.Elem        -> THM.Elem
  | E.Tid         -> THM.Tid
  | E.Addr        -> THM.Addr
  | E.Cell        -> THM.Cell
  | E.SetTh       -> THM.SetTh
  | E.SetInt      -> raise(UnsupportedSort(E.sort_to_str s))
  | E.SetElem     -> THM.SetElem
  | E.SetPair     -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Path        -> THM.Path
  | E.Mem         -> THM.Mem
  | E.Bool        -> THM.Bool
  | E.Int         -> THM.Int
  | E.Pair        -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Array       -> raise(UnsupportedSort(E.sort_to_str s))
  | E.AddrArray   -> raise(UnsupportedSort(E.sort_to_str s))
  | E.TidArray    -> raise(UnsupportedSort(E.sort_to_str s))
  | E.BucketArray -> THM.BucketArray
  | E.Mark        -> THM.Mark
  | E.Bucket      -> THM.Bucket
  | E.Lock        -> THM.Lock
  | E.LockArray   -> THM.LockArray
  | E.Unknown     -> THM.Unknown


and sort_to_expr_sort (s:THM.sort) : E.sort =
  match s with
  | THM.Set         -> E.Set
  | THM.Elem        -> E.Elem
  | THM.Tid         -> E.Tid
  | THM.Addr        -> E.Addr
  | THM.Cell        -> E.Cell
  | THM.SetTh       -> E.SetTh
  | THM.SetElem     -> E.SetElem
  | THM.Path        -> E.Path
  | THM.Mem         -> E.Mem
  | THM.Int         -> E.Int
  | THM.Bool        -> E.Bool
  | THM.TidArray    -> E.TidArray
  | THM.BucketArray -> E.BucketArray
  | THM.Mark        -> E.Mark
  | THM.Bucket      -> E.Bucket
  | THM.Lock        -> E.Lock
  | THM.LockArray   -> E.LockArray
  | THM.Unknown     -> E.Unknown


and build_term_var (v:E.V.t) : THM.term =
  let thm_v = variable_to_thm_var v in
  match (E.V.sort v) with
    E.Set         -> THM.SetT         (THM.VarSet         thm_v)
  | E.Elem        -> THM.ElemT        (THM.VarElem        thm_v)
  | E.Tid         -> THM.TidT         (THM.VarTh          thm_v)
  | E.Addr        -> THM.AddrT        (THM.VarAddr        thm_v)
  | E.Cell        -> THM.CellT        (THM.VarCell        thm_v)
  | E.SetTh       -> THM.SetThT       (THM.VarSetTh       thm_v)
  | E.SetElem     -> THM.SetElemT     (THM.VarSetElem     thm_v)
  | E.Path        -> THM.PathT        (THM.VarPath        thm_v)
  | E.Int         -> THM.IntT         (THM.VarInt         thm_v)
  | E.Mem         -> THM.MemT         (THM.VarMem         thm_v)
  | E.Mark        -> THM.MarkT        (THM.VarMark        thm_v)
  | E.TidArray    -> THM.TidArrayT    (THM.VarTidArray    thm_v)
  | E.BucketArray -> THM.BucketArrayT (THM.VarBucketArray thm_v)
  | E.Bucket      -> THM.BucketT      (THM.VarBucket      thm_v)
  | _             -> THM.VarT         (thm_v)



and variable_to_thm_var (v:E.V.t) : THM.V.t =
  THM.build_var (E.V.id v)
                (sort_to_thm_sort (E.V.sort v))
                (E.V.is_primed v)
                (shared_to_thm_shared (E.V.parameter v))
                (scope_to_thm_scope (E.V.scope v))
                 ~treat_as_pc:(E.is_pc_var v)


and shared_to_thm_shared (th:E.V.shared_or_local) : THM.V.shared_or_local =
  match th with
  | E.V.Shared  -> THM.V.Shared
  | E.V.Local t -> THM.V.Local (variable_to_thm_var t)


and scope_to_thm_scope (p:E.V.procedure_name) : THM.V.procedure_name =
  match p with
  | E.V.GlobalScope -> THM.V.GlobalScope
  | E.V.Scope proc  -> THM.V.Scope proc


and tid_to_thm_tid (th:E.tid) : THM.tid =
  match th with
    E.VarTh v           -> THM.VarTh (variable_to_thm_var v)
  | E.NoTid             -> THM.NoTid
  | E.CellLockId c      -> THM.CellLockId (cell_to_thm_cell c)
  | E.CellLockIdAt _    -> raise(UnsupportedThmExpr(E.tid_to_str th))
  | E.TidArrayRd _      -> raise(UnsupportedThmExpr(E.tid_to_str th))
  | E.PairTid _         -> raise(UnsupportedThmExpr(E.tid_to_str th))
  | E.BucketTid b       -> THM.BucketTid(bucket_to_thm_bucket b)
  | E.TidArrRd (tt,i)   -> THM.TidArrRd(tidarr_to_thm_tidarr tt,
                                        int_to_thm_int i)
  | E.LockId l          -> THM.LockId(lock_to_thm_lock l)

and lock_to_thm_lock (x:E.lock) : THM.lock =
  match x with
    E.VarLock v        -> THM.VarLock (variable_to_thm_var v)
  | E.LLock (l,t)      -> THM.LLock (lock_to_thm_lock l, tid_to_thm_tid t)
  | E.LUnlock (l)      -> THM.LUnlock (lock_to_thm_lock l)
  | E.LockArrRd (ll,i) -> THM.LockArrRd (lockarr_to_thm_lockarr ll, 
                                         int_to_thm_int i)

and lockarr_to_thm_lockarr (ll:E.lockarr) : THM.lockarr =
  match ll with
    E.VarLockArray v       -> THM.VarLockArray (variable_to_thm_var v)
  | E.LockArrayUp (ll,i,l) -> THM.LockArrayUp (lockarr_to_thm_lockarr ll,
                                               int_to_thm_int i,
                                               lock_to_thm_lock l)

and term_to_thm_term (t:E.term) : THM.term =
  match t with
    E.VarT v          -> THM.VarT (variable_to_thm_var v)
  | E.SetT s          -> THM.SetT (set_to_thm_set s)
  | E.ElemT e         -> THM.ElemT (elem_to_thm_elem e)
  | E.TidT t          -> THM.TidT (tid_to_thm_tid t)
  | E.AddrT a         -> THM.AddrT (addr_to_thm_addr a)
  | E.CellT c         -> THM.CellT (cell_to_thm_cell c)
  | E.SetThT st       -> THM.SetThT (setth_to_thm_setth st)
  | E.SetIntT _       -> raise(UnsupportedThmExpr(E.term_to_str t))
  | E.SetElemT st     -> THM.SetElemT (setelem_to_thm_setelem st)
  | E.SetPairT _      -> raise(UnsupportedThmExpr(E.term_to_str t))
  | E.PathT p         -> THM.PathT (path_to_thm_path p)
  | E.MemT m          -> THM.MemT (mem_to_thm_mem m)
  | E.IntT i          -> THM.IntT (int_to_thm_int i)
  | E.PairT _         -> raise(UnsupportedThmExpr(E.term_to_str t))
  | E.AddrArrayT _    -> raise(UnsupportedThmExpr(E.term_to_str t))
  | E.TidArrayT tt    -> THM.TidArrayT (tidarr_to_thm_tidarr tt)
  | E.BucketArrayT bb -> THM.BucketArrayT(bucketarr_to_thm_bucketarr bb)
  | E.MarkT m         -> THM.MarkT (mark_to_thm_mark m)
  | E.BucketT b       -> THM.BucketT (bucket_to_thm_bucket b)
  | E.LockT l         -> THM.LockT (lock_to_thm_lock l)
  | E.LockArrayT ll   -> THM.LockArrayT (lockarr_to_thm_lockarr ll)
  | E.ArrayT a        -> arrays_to_thm_term a


and arrays_to_thm_term (a:E.arrays) : THM.term =
  match a with
  | E.VarArray v -> build_term_var v
  | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
      let thm_v  = variable_to_thm_var v in
      let thm_th = tid_to_thm_tid th_p in
      let thm_t  = term_to_thm_term t
      in
        THM.VarUpdate (thm_v, thm_th, thm_t)
  | E.ArrayUp (_,_,e) -> raise(UnsupportedThmExpr(E.expr_to_str e))


and eq_to_thm_eq ((t1,t2):E.eq) : THM.eq =
  (term_to_thm_term t1, term_to_thm_term t2)


and diseq_to_thm_eq ((t1,t2):E.diseq) : THM.diseq =
  (term_to_thm_term t1, term_to_thm_term t2)


and set_to_thm_set (s:E.set) : THM.set =
  let to_set = set_to_thm_set in
  match s with
    E.VarSet v        -> THM.VarSet (variable_to_thm_var v)
  | E.EmptySet        -> THM.EmptySet
  | E.Singl a         -> THM.Singl (addr_to_thm_addr a)
  | E.Union (s1,s2)   -> THM.Union (to_set s1, to_set s2)
  | E.Intr (s1,s2)    -> THM.Intr (to_set s1, to_set s2)
  | E.Setdiff (s1,s2) -> THM.Setdiff (to_set s1, to_set s2)
  | E.PathToSet p     -> THM.PathToSet (path_to_thm_path p)
  | E.AddrToSet (m,a) -> THM.AddrToSet (mem_to_thm_mem m, addr_to_thm_addr a)
  | E.AddrToSetAt _   -> raise(UnsupportedThmExpr(E.set_to_str s))
  | E.SetArrayRd (E.VarArray v,t) ->
      THM.VarSet (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetArrayRd _    -> raise(UnsupportedThmExpr(E.set_to_str s))
  | E.BucketRegion b  -> THM.BucketRegion(bucket_to_thm_bucket b)


and elem_to_thm_elem (e:E.elem) : THM.elem =
  match e with
    E.VarElem v              -> THM.VarElem (variable_to_thm_var v)
  | E.CellData c             -> THM.CellData (cell_to_thm_cell c)
  | E.ElemArrayRd (E.VarArray v,t) ->
      THM.VarElem (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.ElemArrayRd _          -> raise(UnsupportedThmExpr(E.elem_to_str e))
  | E.HavocListElem          -> THM.HavocListElem
  | E.HavocSkiplistElem      -> raise(UnsupportedThmExpr(E.elem_to_str e))
  | E.LowestElem             -> THM.LowestElem
  | E.HighestElem            -> THM.HighestElem


and addr_to_thm_addr (a:E.addr) : THM.addr =
  match a with
    E.VarAddr v              -> THM.VarAddr (variable_to_thm_var v)
  | E.Null                   -> THM.Null
  | E.Next c                 -> THM.Next (cell_to_thm_cell c)
  | E.NextAt _               -> raise(UnsupportedThmExpr(E.addr_to_str a))
  | E.ArrAt _                -> raise(UnsupportedThmExpr(E.addr_to_str a))
  | E.FirstLocked (m,p)      -> THM.FirstLocked (mem_to_thm_mem m,
                                                    path_to_thm_path p)
  | E.FirstLockedAt _        -> raise(UnsupportedThmExpr(E.addr_to_str a))
  | E.LastLocked (m,p)       -> THM.LastLocked (mem_to_thm_mem m,
                                                path_to_thm_path p)
  | E.AddrArrayRd (E.VarArray v,t) ->
      THM.VarAddr (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.AddrArrayRd _          -> raise(UnsupportedThmExpr(E.addr_to_str a))
  | E.AddrArrRd _            -> raise(UnsupportedThmExpr(E.addr_to_str a))
  | E.BucketInit b           -> THM.BucketInit(bucket_to_thm_bucket b)
  | E.BucketEnd b             -> THM.BucketEnd(bucket_to_thm_bucket b)


and cell_to_thm_cell (c:E.cell) : THM.cell =
  match c with
    E.VarCell v            -> THM.VarCell (variable_to_thm_var v)
  | E.Error                -> THM.Error
  | E.MkCell (e,a,t)       -> THM.MkCell (elem_to_thm_elem e,
                                          addr_to_thm_addr a,
                                          tid_to_thm_tid t)
  | E.MkCellMark (e,a,t,m) -> THM.MkCellMark (elem_to_thm_elem e,
                                              addr_to_thm_addr a,
                                              tid_to_thm_tid t,
                                              mark_to_thm_mark m)
  | E.MkSLKCell _          -> raise(UnsupportedThmExpr(E.cell_to_str c))
  | E.MkSLCell _           -> raise(UnsupportedThmExpr(E.cell_to_str c))
  (* Thm receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | E.CellLock (c,t)       -> THM.CellLock (cell_to_thm_cell c, tid_to_thm_tid t)
  | E.CellLockAt _         -> raise(UnsupportedThmExpr(E.cell_to_str c))
  | E.CellUnlock c         -> THM.CellUnlock (cell_to_thm_cell c)
  | E.CellUnlockAt _       -> raise(UnsupportedThmExpr(E.cell_to_str c))
  | E.CellAt (m,a)         -> THM.CellAt (mem_to_thm_mem m, addr_to_thm_addr a)
  | E.CellArrayRd (E.VarArray v,t) ->
      THM.VarCell (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.CellArrayRd _        -> raise(UnsupportedThmExpr(E.cell_to_str c))
  | E.UpdCellAddr _        -> raise(UnsupportedThmExpr(E.cell_to_str c))


and mark_to_thm_mark (m:E.mark) : THM.mark =
  match m with
    E.VarMark v -> THM.VarMark (variable_to_thm_var v)
  | E.MarkTrue  -> THM.MarkTrue
  | E.MarkFalse -> THM.MarkFalse
  | E.Marked c  -> THM.Marked (cell_to_thm_cell c)


and bucket_to_thm_bucket (bb:E.bucket) : THM.bucket =
  match bb with
    E.VarBucket v -> THM.VarBucket (variable_to_thm_var v)
  | E.MkBucket (i,e,s,t) -> THM.MkBucket(addr_to_thm_addr i,
                                         addr_to_thm_addr e,
                                         set_to_thm_set s,
                                         tid_to_thm_tid t)
  | E.BucketArrRd (bb,i) -> THM.BucketArrRd (bucketarr_to_thm_bucketarr bb,
                                             int_to_thm_int i)


and setth_to_thm_setth (st:E.setth) : THM.setth =
  let to_setth = setth_to_thm_setth in
  match st with
    E.VarSetTh v        -> THM.VarSetTh (variable_to_thm_var v)
  | E.EmptySetTh        -> THM.EmptySetTh
  | E.SinglTh t         -> THM.SinglTh (tid_to_thm_tid t)
  | E.UnionTh (s1,s2)   -> THM.UnionTh (to_setth s1, to_setth s2)
  | E.IntrTh (s1,s2)    -> THM.IntrTh (to_setth s1, to_setth s2)
  | E.SetdiffTh (s1,s2) -> THM.SetdiffTh (to_setth s1, to_setth s2)
  | E.SetThArrayRd (E.VarArray v,t) ->
      THM.VarSetTh (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetThArrayRd _    -> raise(UnsupportedThmExpr(E.setth_to_str st))
  | E.LockSet (m,p)     -> THM.LockSet (mem_to_thm_mem m,
                                        path_to_thm_path p)


and setelem_to_thm_setelem (st:E.setelem) : THM.setelem =
  let to_setelem = setelem_to_thm_setelem in
  match st with
    E.VarSetElem v        -> THM.VarSetElem (variable_to_thm_var v)
  | E.EmptySetElem        -> THM.EmptySetElem
  | E.SinglElem e         -> THM.SinglElem (elem_to_thm_elem e)
  | E.UnionElem (s1,s2)   -> THM.UnionElem (to_setelem s1, to_setelem s2)
  | E.IntrElem (s1,s2)    -> THM.IntrElem (to_setelem s1, to_setelem s2)
  | E.SetdiffElem (s1,s2) -> THM.SetdiffElem (to_setelem s1, to_setelem s2)
  | E.SetElemArrayRd (E.VarArray v,t) ->
      THM.VarSetElem (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetToElems (s,m)    -> THM.SetToElems (set_to_thm_set s,
                                                mem_to_thm_mem m)
  | E.SetElemArrayRd _    -> raise(UnsupportedThmExpr(E.setelem_to_str st))


and path_to_thm_path (p:E.path) : THM.path =
  match p with
    E.VarPath v         -> THM.VarPath (variable_to_thm_var v)
  | E.Epsilon           -> THM.Epsilon
  | E.SimplePath a      -> THM.SimplePath (addr_to_thm_addr a)
  | E.GetPath (m,a1,a2) -> THM.GetPath (mem_to_thm_mem m,
                                           addr_to_thm_addr a1,
                                           addr_to_thm_addr a2)
  | E.GetPathAt _       -> raise(UnsupportedThmExpr(E.path_to_str p))
  | E.PathArrayRd _     -> raise(UnsupportedThmExpr(E.path_to_str p))


and mem_to_thm_mem (m:E.mem) : THM.mem =
  match m with
    E.VarMem v       -> THM.VarMem (variable_to_thm_var v)
  | E.Update (m,a,c) -> THM.Update (mem_to_thm_mem m,
                                       addr_to_thm_addr a,
                                       cell_to_thm_cell c)
  (* Missing the case for "emp" *)
  | E.MemArrayRd (E.VarArray v,t) ->
      THM.VarMem (variable_to_thm_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.MemArrayRd _        -> raise(UnsupportedThmExpr(E.mem_to_str m))


and int_to_thm_int (i:E.integer) : THM.integer =
  match i with
    E.IntVal n -> THM.IntVal n
  | E.VarInt v -> THM.VarInt (variable_to_thm_var v)
  | E.IntNeg j -> THM.IntNeg (int_to_thm_int j)
  | E.IntAdd (j1,j2) -> THM.IntAdd (int_to_thm_int j1, int_to_thm_int j2)
  | E.IntSub (j1,j2) -> THM.IntSub (int_to_thm_int j1, int_to_thm_int j2)
  | E.IntMul (j1,j2) -> THM.IntMul (int_to_thm_int j1, int_to_thm_int j2)
  | E.IntDiv (j1,j2) -> THM.IntDiv (int_to_thm_int j1, int_to_thm_int j2)
  | E.IntMod (j1,j2) -> THM.IntMod (int_to_thm_int j1, int_to_thm_int j2)
  | E.IntArrayRd _   -> raise(UnsupportedThmExpr(E.integer_to_str i))
  | E.IntSetMin _    -> raise(UnsupportedThmExpr(E.integer_to_str i))
  | E.IntSetMax _    -> raise(UnsupportedThmExpr(E.integer_to_str i))
  | E.CellMax _      -> raise(UnsupportedThmExpr(E.integer_to_str i))
  | E.HavocLevel     -> raise(UnsupportedThmExpr(E.integer_to_str i))
  | E.HashCode e     -> THM.HashCode(elem_to_thm_elem e)
  | E.PairInt _      -> raise(UnsupportedThmExpr(E.integer_to_str i))


and tidarr_to_thm_tidarr (tt:E.tidarr) : THM.tidarr =
  match tt with
    E.VarTidArray v -> THM.VarTidArray (variable_to_thm_var v)
  | E.TidArrayUp (tt,i,t) -> THM.TidArrayUp (tidarr_to_thm_tidarr tt,
                                             int_to_thm_int i,
                                             tid_to_thm_tid t)
  | E.CellTids c          -> raise(UnsupportedThmExpr(E.tidarr_to_str tt))


and bucketarr_to_thm_bucketarr (bb:E.bucketarr) : THM.bucketarr =
  match bb with
    E.VarBucketArray v -> THM.VarBucketArray (variable_to_thm_var v)
  | E.BucketArrayUp (bb,i,b) -> THM.BucketArrayUp (bucketarr_to_thm_bucketarr bb,
                                                   int_to_thm_int i,
                                                   bucket_to_thm_bucket b)


and atom_to_thm_atom (a:E.atom) : THM.atom =
  let path      = path_to_thm_path       in
  let mem       = mem_to_thm_mem         in
  let addr      = addr_to_thm_addr       in
  let elem      = elem_to_thm_elem       in
  let set       = set_to_thm_set         in
  let tid       = tid_to_thm_tid         in
  let setth     = setth_to_thm_setth     in
  let setelem   = setelem_to_thm_setelem in
  let bucketarr = bucketarr_to_thm_bucketarr in
  let integer   = int_to_thm_int in
  let term      = term_to_thm_term       in
  match a with
    E.Append (p1,p2,p3)    -> THM.Append (path p1,path p2,path p3)
  | E.Reach (m,a1,a2,p)    -> THM.Reach (mem m, addr a1, addr a2, path p)
  | E.ReachAt _            -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.OrderList(m,a1,a2)   -> THM.OrderList (mem m, addr a1, addr a2)
  | E.Skiplist _           -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.Hashmap (m,s,se,bb,i)-> THM.Hashmap(mem m, set s, setelem se,
                                          bucketarr bb, integer i)
  | E.In (a,s)             -> THM.In (addr a, set s)
  | E.SubsetEq (s1,s2)     -> THM.SubsetEq (set s1, set s2)
  | E.InTh (t,s)           -> THM.InTh (tid t, setth s)
  | E.SubsetEqTh (s1,s2)   -> THM.SubsetEqTh (setth s1, setth s2)
  | E.InInt _              -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.SubsetEqInt _        -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.InElem (e,s)         -> THM.InElem (elem_to_thm_elem e, setelem s)
  | E.SubsetEqElem (s1,s2) -> THM.SubsetEqElem (setelem s1, setelem s2)
  | E.InPair _             -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.SubsetEqPair _       -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.InTidPair _          -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.InIntPair _          -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.Less (i1,i2)         -> THM.Less (integer i1, integer i2)
  | E.LessEq (i1,i2)       -> THM.LessEq (integer i1, integer i2)
  | E.Greater (i1,i2)      -> THM.Greater (integer i1, integer i2)
  | E.GreaterEq (i1,i2)    -> THM.GreaterEq (integer i1, integer i2)
  | E.LessTid _            -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.LessElem (e1,e2)     -> THM.LessElem (elem e1, elem e2)
  | E.GreaterElem (e1,e2)  -> THM.GreaterElem (elem e1, elem e2)
  | E.Eq (t1,t2)           -> THM.Eq (term t1, term t2)
  | E.InEq (t1,t2)         -> THM.InEq (term t1, term t2)
  | E.UniqueInt _          -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.UniqueTid _          -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.BoolVar v            -> THM.BoolVar (variable_to_thm_var v)
  | E.BoolArrayRd _        -> raise(UnsupportedThmExpr(E.atom_to_str a))
  | E.PC (pc,t,pr)         -> THM.PC (pc, shared_to_thm_shared t, pr)
  | E.PCUpdate (pc,t)      -> THM.PCUpdate (pc, tid_to_thm_tid t)
  | E.PCRange (pc1,pc2,t,pr) -> THM.PCRange (pc1, pc2, shared_to_thm_shared t, pr)


and literal_to_thm_literal (l:E.literal) : THM.literal =
  Formula.literal_conv atom_to_thm_atom l


and conj_formula_to_thm_conj_formula (cf:E.conjunctive_formula) : THM.conjunctive_formula =
  Formula.conjunctive_formula_conv atom_to_thm_atom cf


and formula_to_thm_formula (phi:E.formula) : THM.formula =
  Formula.formula_conv atom_to_thm_atom phi



  
(* ThmExpression to Expression conversion *)
let rec build_expr_term_var (v:THM.V.t) : E.term =
  let thm_v = var_to_expr_var v in
  match (THM.V.sort v) with
    THM.Set         -> E.SetT         (E.VarSet         thm_v)
  | THM.Elem        -> E.ElemT        (E.VarElem        thm_v)
  | THM.Tid         -> E.TidT         (E.VarTh          thm_v)
  | THM.Addr        -> E.AddrT        (E.VarAddr        thm_v)
  | THM.Cell        -> E.CellT        (E.VarCell        thm_v)
  | THM.SetTh       -> E.SetThT       (E.VarSetTh       thm_v)
  | THM.SetElem     -> E.SetElemT     (E.VarSetElem     thm_v)
  | THM.Path        -> E.PathT        (E.VarPath        thm_v)
  | THM.Int         -> E.IntT         (E.VarInt         thm_v)
  | THM.Mem         -> E.MemT         (E.VarMem         thm_v)
  | THM.Mark        -> E.MarkT        (E.VarMark        thm_v)
  | THM.TidArray    -> E.TidArrayT    (E.VarTidArray    thm_v)
  | THM.BucketArray -> E.BucketArrayT (E.VarBucketArray thm_v)
  | THM.Bucket      -> E.BucketT      (E.VarBucket      thm_v)
  | _               -> E.VarT         (thm_v)



and var_to_expr_var (v:THM.V.t) : E.V.t =
  E.build_var (THM.V.id v)
              (sort_to_expr_sort (THM.V.sort v))
              (THM.V.is_primed v)
              (shared_to_expr_shared (THM.V.parameter v))
              (scope_to_expr_scope (THM.V.scope v))


and shared_to_expr_shared (th:THM.V.shared_or_local) : E.V.shared_or_local =
  match th with
  | THM.V.Shared  -> E.V.Shared
  | THM.V.Local t -> E.V.Local (var_to_expr_var t)


and scope_to_expr_scope (p:THM.V.procedure_name) : E.V.procedure_name =
  match p with
  | THM.V.GlobalScope -> E.V.GlobalScope
  | THM.V.Scope proc  -> E.V.Scope proc


and tid_to_expr_tid (th:THM.tid) : E.tid =
  match th with
    THM.VarTh v           -> E.VarTh (var_to_expr_var v)
  | THM.NoTid             -> E.NoTid
  | THM.CellLockId c      -> E.CellLockId (cell_to_expr_cell c)
  | THM.BucketTid b       -> E.BucketTid(bucket_to_expr_bucket b)
  | THM.TidArrRd (tt,i)   -> E.TidArrRd(tidarr_to_expr_tidarr tt,
                                        int_to_expr_int i)
  | THM.LockId l          -> E.LockId(lock_to_expr_lock l)

and lock_to_expr_lock (x:THM.lock) : E.lock =
  match x with
    THM.VarLock v        -> E.VarLock (var_to_expr_var v)
  | THM.LLock (l,t)      -> E.LLock (lock_to_expr_lock l, tid_to_expr_tid t)
  | THM.LUnlock (l)      -> E.LUnlock (lock_to_expr_lock l)
  | THM.LockArrRd (ll,i) -> E.LockArrRd (lockarr_to_expr_lockarr ll, 
                                         int_to_expr_int i)

and lockarr_to_expr_lockarr (ll:THM.lockarr) : E.lockarr =
  match ll with
    THM.VarLockArray v       -> E.VarLockArray (var_to_expr_var v)
  | THM.LockArrayUp (ll,i,l) -> E.LockArrayUp (lockarr_to_expr_lockarr ll,
                                               int_to_expr_int i,
                                               lock_to_expr_lock l)

and term_to_expr_term (t:THM.term) : E.term =
  match t with
    THM.VarT v          -> E.VarT (var_to_expr_var v)
  | THM.SetT s          -> E.SetT (set_to_expr_set s)
  | THM.ElemT e         -> E.ElemT (elem_to_expr_elem e)
  | THM.TidT t          -> E.TidT (tid_to_expr_tid t)
  | THM.AddrT a         -> E.AddrT (addr_to_expr_addr a)
  | THM.CellT c         -> E.CellT (cell_to_expr_cell c)
  | THM.SetThT st       -> E.SetThT (setth_to_expr_setth st)
  | THM.SetElemT st     -> E.SetElemT (setelem_to_expr_setelem st)
  | THM.PathT p         -> E.PathT (path_to_expr_path p)
  | THM.MemT m          -> E.MemT (mem_to_expr_mem m)
  | THM.IntT i          -> E.IntT (int_to_expr_int i)
  | THM.TidArrayT tt    -> E.TidArrayT (tidarr_to_expr_tidarr tt)
  | THM.BucketArrayT bb -> E.BucketArrayT(bucketarr_to_expr_bucketarr bb)
  | THM.MarkT m         -> E.MarkT (mark_to_expr_mark m)
  | THM.BucketT b       -> E.BucketT (bucket_to_expr_bucket b)
  | THM.LockT l         -> E.LockT (lock_to_expr_lock l)
  | THM.LockArrayT ll   -> E.LockArrayT (lockarr_to_expr_lockarr ll)
  | THM.VarUpdate (v,th,t) ->
      let expr_a  = E.VarArray (var_to_expr_var v) in
      let expr_th = tid_to_expr_tid th in
      let expr_t  = E.Term (term_to_expr_term t)
      in
        E.ArrayT (E.ArrayUp (expr_a, expr_th, expr_t))


and eq_to_expr_eq ((t1,t2):THM.eq) : E.eq =
  (term_to_expr_term t1, term_to_expr_term t2)


and diseq_to_expr_eq ((t1,t2):THM.diseq) : E.diseq =
  (term_to_expr_term t1, term_to_expr_term t2)


and set_to_expr_set (s:THM.set) : E.set =
  let to_set = set_to_expr_set in
  match s with
    THM.VarSet v        -> E.VarSet (var_to_expr_var v)
  | THM.EmptySet        -> E.EmptySet
  | THM.Singl a         -> E.Singl (addr_to_expr_addr a)
  | THM.Union (s1,s2)   -> E.Union (to_set s1, to_set s2)
  | THM.Intr (s1,s2)    -> E.Intr (to_set s1, to_set s2)
  | THM.Setdiff (s1,s2) -> E.Setdiff (to_set s1, to_set s2)
  | THM.PathToSet p     -> E.PathToSet (path_to_expr_path p)
  | THM.AddrToSet (m,a) -> E.AddrToSet (mem_to_expr_mem m, addr_to_expr_addr a)
  | THM.BucketRegion b  -> E.BucketRegion(bucket_to_expr_bucket b)


and elem_to_expr_elem (e:THM.elem) : E.elem =
  match e with
    THM.VarElem v              -> E.VarElem (var_to_expr_var v)
  | THM.CellData c             -> E.CellData (cell_to_expr_cell c)
  | THM.HavocListElem          -> E.HavocListElem
  | THM.LowestElem             -> E.LowestElem
  | THM.HighestElem            -> E.HighestElem


and addr_to_expr_addr (a:THM.addr) : E.addr =
  match a with
    THM.VarAddr v              -> E.VarAddr (var_to_expr_var v)
  | THM.Null                   -> E.Null
  | THM.Next c                 -> E.Next (cell_to_expr_cell c)
  | THM.FirstLocked (m,p)      -> E.FirstLocked (mem_to_expr_mem m,
                                                    path_to_expr_path p)
  | THM.LastLocked (m,p)       -> E.LastLocked (mem_to_expr_mem m,
                                                path_to_expr_path p)
  | THM.BucketInit b           -> E.BucketInit(bucket_to_expr_bucket b)
  | THM.BucketEnd b            -> E.BucketEnd(bucket_to_expr_bucket b)


and cell_to_expr_cell (c:THM.cell) : E.cell =
  match c with
    THM.VarCell v            -> E.VarCell (var_to_expr_var v)
  | THM.Error                -> E.Error
  | THM.MkCell (e,a,t)       -> E.MkCell (elem_to_expr_elem e,
                                          addr_to_expr_addr a,
                                          tid_to_expr_tid t)
  | THM.MkCellMark (e,a,t,m) -> E.MkCellMark (elem_to_expr_elem e,
                                              addr_to_expr_addr a,
                                              tid_to_expr_tid t,
                                              mark_to_expr_mark m)
  (* Thm receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | THM.CellLock (c,t)       -> E.CellLock (cell_to_expr_cell c, tid_to_expr_tid t)
  | THM.CellUnlock c         -> E.CellUnlock (cell_to_expr_cell c)
  | THM.CellAt (m,a)         -> E.CellAt (mem_to_expr_mem m, addr_to_expr_addr a)


and mark_to_expr_mark (m:THM.mark) : E.mark =
  match m with
    THM.VarMark v -> E.VarMark (var_to_expr_var v)
  | THM.MarkTrue  -> E.MarkTrue
  | THM.MarkFalse -> E.MarkFalse
  | THM.Marked c  -> E.Marked (cell_to_expr_cell c)


and bucket_to_expr_bucket (bb:THM.bucket) : E.bucket =
  match bb with
    THM.VarBucket v -> E.VarBucket (var_to_expr_var v)
  | THM.MkBucket (i,e,s,t) -> E.MkBucket(addr_to_expr_addr i,
                                         addr_to_expr_addr e,
                                         set_to_expr_set s,
                                         tid_to_expr_tid t)
  | THM.BucketArrRd (bb,i) -> E.BucketArrRd (bucketarr_to_expr_bucketarr bb,
                                             int_to_expr_int i)


and setth_to_expr_setth (st:THM.setth) : E.setth =
  let to_setth = setth_to_expr_setth in
  match st with
    THM.VarSetTh v        -> E.VarSetTh (var_to_expr_var v)
  | THM.EmptySetTh        -> E.EmptySetTh
  | THM.SinglTh t         -> E.SinglTh (tid_to_expr_tid t)
  | THM.UnionTh (s1,s2)   -> E.UnionTh (to_setth s1, to_setth s2)
  | THM.IntrTh (s1,s2)    -> E.IntrTh (to_setth s1, to_setth s2)
  | THM.SetdiffTh (s1,s2) -> E.SetdiffTh (to_setth s1, to_setth s2)
  | THM.LockSet (m,p)     -> E.LockSet (mem_to_expr_mem m,
                                        path_to_expr_path p)


and setelem_to_expr_setelem (st:THM.setelem) : E.setelem =
  let to_setelem = setelem_to_expr_setelem in
  match st with
    THM.VarSetElem v        -> E.VarSetElem (var_to_expr_var v)
  | THM.EmptySetElem        -> E.EmptySetElem
  | THM.SinglElem e         -> E.SinglElem (elem_to_expr_elem e)
  | THM.UnionElem (s1,s2)   -> E.UnionElem (to_setelem s1, to_setelem s2)
  | THM.IntrElem (s1,s2)    -> E.IntrElem (to_setelem s1, to_setelem s2)
  | THM.SetdiffElem (s1,s2) -> E.SetdiffElem (to_setelem s1, to_setelem s2)
  | THM.SetToElems (s,m)    -> E.SetToElems (set_to_expr_set s,
                                                mem_to_expr_mem m)


and path_to_expr_path (p:THM.path) : E.path =
  match p with
    THM.VarPath v         -> E.VarPath (var_to_expr_var v)
  | THM.Epsilon           -> E.Epsilon
  | THM.SimplePath a      -> E.SimplePath (addr_to_expr_addr a)
  | THM.GetPath (m,a1,a2) -> E.GetPath (mem_to_expr_mem m,
                                           addr_to_expr_addr a1,
                                           addr_to_expr_addr a2)


and mem_to_expr_mem (m:THM.mem) : E.mem =
  match m with
    THM.VarMem v       -> E.VarMem (var_to_expr_var v)
  | THM.Update (m,a,c) -> E.Update (mem_to_expr_mem m,
                                       addr_to_expr_addr a,
                                       cell_to_expr_cell c)


and int_to_expr_int (i:THM.integer) : E.integer =
  match i with
    THM.IntVal n -> E.IntVal n
  | THM.VarInt v -> E.VarInt (var_to_expr_var v)
  | THM.IntNeg j -> E.IntNeg (int_to_expr_int j)
  | THM.IntAdd (j1,j2) -> E.IntAdd (int_to_expr_int j1, int_to_expr_int j2)
  | THM.IntSub (j1,j2) -> E.IntSub (int_to_expr_int j1, int_to_expr_int j2)
  | THM.IntMul (j1,j2) -> E.IntMul (int_to_expr_int j1, int_to_expr_int j2)
  | THM.IntDiv (j1,j2) -> E.IntDiv (int_to_expr_int j1, int_to_expr_int j2)
  | THM.IntMod (j1,j2) -> E.IntMod (int_to_expr_int j1, int_to_expr_int j2)
  | THM.HashCode e     -> E.HashCode(elem_to_expr_elem e)


and tidarr_to_expr_tidarr (tt:THM.tidarr) : E.tidarr =
  match tt with
    THM.VarTidArray v -> E.VarTidArray (var_to_expr_var v)
  | THM.TidArrayUp (tt,i,t) -> E.TidArrayUp (tidarr_to_expr_tidarr tt,
                                             int_to_expr_int i,
                                             tid_to_expr_tid t)


and bucketarr_to_expr_bucketarr (bb:THM.bucketarr) : E.bucketarr =
  match bb with
    THM.VarBucketArray v -> E.VarBucketArray (var_to_expr_var v)
  | THM.BucketArrayUp (bb,i,b) -> E.BucketArrayUp (bucketarr_to_expr_bucketarr bb,
                                                   int_to_expr_int i,
                                                   bucket_to_expr_bucket b)


and atom_to_expr_atom (a:THM.atom) : E.atom =
  let path      = path_to_expr_path       in
  let mem       = mem_to_expr_mem         in
  let addr      = addr_to_expr_addr       in
  let elem      = elem_to_expr_elem       in
  let set       = set_to_expr_set         in
  let tid       = tid_to_expr_tid         in
  let setth     = setth_to_expr_setth     in
  let setelem   = setelem_to_expr_setelem in
  let bucketarr = bucketarr_to_expr_bucketarr in
  let integer   = int_to_expr_int in
  let term      = term_to_expr_term       in
  match a with
    THM.Append (p1,p2,p3)    -> E.Append (path p1,path p2,path p3)
  | THM.Reach (m,a1,a2,p)    -> E.Reach (mem m, addr a1, addr a2, path p)
  | THM.OrderList(m,a1,a2)   -> E.OrderList (mem m, addr a1, addr a2)
  | THM.Hashmap (m,s,se,bb,i)-> E.Hashmap(mem m, set s, setelem se,
                                          bucketarr bb, integer i)
  | THM.In (a,s)             -> E.In (addr a, set s)
  | THM.SubsetEq (s1,s2)     -> E.SubsetEq (set s1, set s2)
  | THM.InTh (t,s)           -> E.InTh (tid t, setth s)
  | THM.SubsetEqTh (s1,s2)   -> E.SubsetEqTh (setth s1, setth s2)
  | THM.InElem (e,s)         -> E.InElem (elem_to_expr_elem e, setelem s)
  | THM.SubsetEqElem (s1,s2) -> E.SubsetEqElem (setelem s1, setelem s2)
  | THM.Less (i1,i2)         -> E.Less (integer i1, integer i2)
  | THM.LessEq (i1,i2)       -> E.LessEq (integer i1, integer i2)
  | THM.Greater (i1,i2)      -> E.Greater (integer i1, integer i2)
  | THM.GreaterEq (i1,i2)    -> E.GreaterEq (integer i1, integer i2)
  | THM.LessElem (e1,e2)     -> E.LessElem (elem e1, elem e2)
  | THM.GreaterElem (e1,e2)  -> E.GreaterElem (elem e1, elem e2)
  | THM.Eq (t1,t2)           -> E.Eq (term t1, term t2)
  | THM.InEq (t1,t2)         -> E.InEq (term t1, term t2)
  | THM.BoolVar v            -> E.BoolVar (var_to_expr_var v)
  | THM.PC (pc,t,pr)         -> E.PC (pc, shared_to_expr_shared t, pr)
  | THM.PCUpdate (pc,t)      -> E.PCUpdate (pc, tid_to_expr_tid t)
  | THM.PCRange (pc1,pc2,t,pr) -> E.PCRange (pc1, pc2, shared_to_expr_shared t, pr)

and literal_to_expr_literal (l:THM.literal) : E.literal =
  Formula.literal_conv atom_to_expr_atom l


and conj_formula_to_expr_conj_formula (cf:THM.conjunctive_formula) : E.conjunctive_formula =
  Formula.conjunctive_formula_conv atom_to_expr_atom cf


and formula_to_expr_formula (phi:THM.formula) : E.formula =
  Formula.formula_conv atom_to_expr_atom phi
