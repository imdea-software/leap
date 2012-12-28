open LeapLib



module Make (TSLK : TSLKExpression.S) =
  struct

    module Expr = Expression

    type varId = Expr.varId
    type sort  = Expr.sort
    type tid   = Expr.tid

    exception UnsupportedSort of string
    exception UnsupportedTSLKExpr of string


    (* Expression to TSLKExpression conversion *)


    let rec sort_to_tslk_sort (s:Expr.sort) : TSLK.sort =
      match s with
        Expr.Set       -> TSLK.Set
      | Expr.Elem      -> TSLK.Elem
      | Expr.Thid      -> TSLK.Thid
      | Expr.Addr      -> TSLK.Addr
      | Expr.Cell      -> TSLK.Cell
      | Expr.SetTh     -> TSLK.SetTh
      | Expr.SetInt    -> raise (UnsupportedSort (Expr.sort_to_str s))
      | Expr.SetElem   -> TSLK.SetElem
      | Expr.Path      -> TSLK.Path
      | Expr.Mem       -> TSLK.Mem
      | Expr.Bool      -> raise (UnsupportedSort (Expr.sort_to_str s))
      | Expr.Int       -> TSLK.Level
      | Expr.Array     -> raise (UnsupportedSort (Expr.sort_to_str s))
      | Expr.AddrArray -> raise (UnsupportedSort (Expr.sort_to_str s))
      | Expr.TidArray  -> raise (UnsupportedSort (Expr.sort_to_str s))
      | Expr.Unknown   -> TSLK.Unknown


    and sort_to_expr_sort (s:TSLK.sort) : Expr.sort =
      match s with
      | TSLK.Set     -> Expr.Set
      | TSLK.Elem    -> Expr.Elem
      | TSLK.Thid    -> Expr.Thid
      | TSLK.Addr    -> Expr.Addr
      | TSLK.Cell    -> Expr.Cell
      | TSLK.SetTh   -> Expr.SetTh
      | TSLK.SetElem -> Expr.SetElem
      | TSLK.Path    -> Expr.Path
      | TSLK.Mem     -> Expr.Mem
      | TSLK.Level   -> Expr.Int
      | TSLK.Unknown -> Expr.Unknown


    and build_term_var (v:Expr.variable) : TSLK.term =
      let tslk_v = variable_to_tslk_var v in
      match Expr.var_sort v with
        Expr.Set       -> TSLK.SetT       (TSLK.VarSet        tslk_v)
      | Expr.Elem      -> TSLK.ElemT      (TSLK.VarElem       tslk_v)
      | Expr.Thid      -> TSLK.ThidT      (TSLK.VarTh         tslk_v)
      | Expr.Addr      -> TSLK.AddrT      (TSLK.VarAddr       tslk_v)
      | Expr.Cell      -> TSLK.CellT      (TSLK.VarCell       tslk_v)
      | Expr.SetTh     -> TSLK.SetThT     (TSLK.VarSetTh      tslk_v)
      | Expr.Path      -> TSLK.PathT      (TSLK.VarPath       tslk_v)
      | Expr.Mem       -> TSLK.MemT       (TSLK.VarMem        tslk_v)
      | Expr.Int       -> TSLK.LevelT     (TSLK.VarLevel      tslk_v)
      | _              -> TSLK.VarT       (tslk_v)



    and variable_to_tslk_var (v:Expr.variable) : TSLK.variable =
      let (id,s,pr,th,p,_) = v
      in
        (id, sort_to_tslk_sort s, pr, Option.lift tid_to_tslk_tid th, p)



    and tid_to_tslk_tid (th:Expr.tid) : TSLK.tid =
      match th with
        Expr.VarTh v            -> TSLK.VarTh (variable_to_tslk_var v)
      | Expr.NoThid             -> TSLK.NoThid
      | Expr.CellLockId _       -> raise (UnsupportedTSLKExpr(Expr.tid_to_str th))
      | Expr.CellLockIdAt (c,l) -> TSLK.CellLockIdAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l)
      | Expr.ThidArrayRd _      -> raise (UnsupportedTSLKExpr(Expr.tid_to_str th))
      | Expr.ThidArrRd (tt,i)   -> raise (UnsupportedTSLKExpr(Expr.tid_to_str th))

    and term_to_tslk_term (t:Expr.term) : TSLK.term =
      match t with
        Expr.VarT v        -> TSLK.VarT (variable_to_tslk_var v)
      | Expr.SetT s        -> TSLK.SetT (set_to_tslk_set s)
      | Expr.ElemT e       -> TSLK.ElemT (elem_to_tslk_elem e)
      | Expr.ThidT t       -> TSLK.ThidT (tid_to_tslk_tid t)
      | Expr.AddrT a       -> TSLK.AddrT (addr_to_tslk_addr a)
      | Expr.CellT c       -> TSLK.CellT (cell_to_tslk_cell c)
      | Expr.SetThT st     -> TSLK.SetThT (setth_to_tslk_setth st)
      | Expr.SetIntT _     -> raise(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.SetElemT st   -> TSLK.SetElemT (setelem_to_tslk_setelem st)
      | Expr.PathT p       -> TSLK.PathT (path_to_tslk_path p)
      | Expr.MemT m        -> TSLK.MemT (mem_to_tslk_mem m)
      | Expr.IntT i        -> TSLK.LevelT (int_to_tslk_level i)
      | Expr.AddrArrayT aa -> raise(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.TidArrayT tt  -> raise(UnsupportedTSLKExpr(Expr.term_to_str t))
      | Expr.ArrayT a      -> raise(UnsupportedTSLKExpr(Expr.term_to_str t))


    and eq_to_tslk_eq ((t1,t2):Expr.eq) : TSLK.eq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


    and diseq_to_tslk_eq ((t1,t2):Expr.diseq) : TSLK.diseq =
      (term_to_tslk_term t1, term_to_tslk_term t2)


    and set_to_tslk_set (s:Expr.set) : TSLK.set =
      let to_set = set_to_tslk_set in
      match s with
        Expr.VarSet v            -> TSLK.VarSet (variable_to_tslk_var v)
      | Expr.EmptySet            -> TSLK.EmptySet
      | Expr.Singl a             -> TSLK.Singl (addr_to_tslk_addr a)
      | Expr.Union (s1,s2)       -> TSLK.Union (to_set s1, to_set s2)
      | Expr.Intr (s1,s2)        -> TSLK.Intr (to_set s1, to_set s2)
      | Expr.Setdiff (s1,s2)     -> TSLK.Setdiff (to_set s1, to_set s2)
      | Expr.PathToSet p         -> TSLK.PathToSet (path_to_tslk_path p)
      | Expr.AddrToSet _         -> raise(UnsupportedTSLKExpr(Expr.set_to_str s))
      | Expr.AddrToSetAt (m,a,l) -> TSLK.AddrToSet (mem_to_tslk_mem m,
                                                    addr_to_tslk_addr a,
                                                    int_to_tslk_level l)
      | Expr.SetArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSet (variable_to_tslk_var v)
      | Expr.SetArrayRd _        -> raise (UnsupportedTSLKExpr (Expr.set_to_str s))


    and elem_to_tslk_elem (e:Expr.elem) : TSLK.elem =
      match e with
        Expr.VarElem v              -> TSLK.VarElem (variable_to_tslk_var v)
      | Expr.CellData c             -> TSLK.CellData (cell_to_tslk_cell c)
      | Expr.ElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarElem (variable_to_tslk_var v)
      | Expr.ElemArrayRd _          -> raise(UnsupportedTSLKExpr(Expr.elem_to_str e))
      | Expr.HavocListElem          -> raise(UnsupportedTSLKExpr(Expr.elem_to_str e))
      | Expr.HavocSkiplistElem      -> TSLK.HavocSkiplistElem
      | Expr.LowestElem             -> TSLK.LowestElem
      | Expr.HighestElem            -> TSLK.HighestElem


    and addr_to_tslk_addr (a:Expr.addr) : TSLK.addr =
      match a with
        Expr.VarAddr v              -> TSLK.VarAddr (variable_to_tslk_var v)
      | Expr.Null                   -> TSLK.Null
      | Expr.Next _                 -> raise(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.NextAt (c,l)           -> TSLK.NextAt (cell_to_tslk_cell c, int_to_tslk_level l)
      | Expr.FirstLocked (m,p)      -> raise(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.FirstLockedAt (m,p,l)  -> TSLK.FirstLockedAt (mem_to_tslk_mem m,
                                                          path_to_tslk_path p,
                                                          int_to_tslk_level l)
      | Expr.AddrArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarAddr (variable_to_tslk_var v)
      | Expr.AddrArrayRd _          -> raise(UnsupportedTSLKExpr(Expr.addr_to_str a))
      | Expr.AddrArrRd (aa,i)       -> raise(UnsupportedTSLKExpr(Expr.addr_to_str a))


    and cell_to_tslk_cell (c:Expr.cell) : TSLK.cell =
      match c with
        Expr.VarCell v            -> TSLK.VarCell (variable_to_tslk_var v)
      | Expr.Error                -> TSLK.Error
      | Expr.MkCell _             -> raise(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.MkSLKCell (e,aa,tt,l)->
          if List.length aa > TSLK.k || List.length tt > TSLK.k then
            begin
              Interface.Err.msg "Too many addresses or threads ids in MkCell" $
                Printf.sprintf "Tried to build a term:\n%s\n while in TSLK[%i]. \
                                Notice the number of addresses or threads identifiers \
                                exceeds the parameter of the theory."
                                (Expr.cell_to_str c) TSLK.k;
              raise(UnsupportedTSLKExpr(Expr.cell_to_str c))
            end
          else
            TSLK.MkCell (elem_to_tslk_elem e,
                         List.map addr_to_tslk_addr aa,
                         List.map tid_to_tslk_tid tt,
                         int_to_tslk_level l)
      | Expr.MkSLCell (e,aa,tt,l) -> raise(UnsupportedTSLKExpr(Expr.cell_to_str c))
      (* TSLK receives two arguments, while current epxression receives only one *)
      (* However, for the list examples, I think we will not need it *)
      | Expr.CellLock _           -> raise(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.CellLockAt (c,l,t)   -> TSLK.CellLockAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l,
                                                     tid_to_tslk_tid t)
      | Expr.CellUnlock _         -> raise(UnsupportedTSLKExpr(Expr.cell_to_str c))
      | Expr.CellUnlockAt (c,l)   -> TSLK.CellUnlockAt (cell_to_tslk_cell c,
                                                       int_to_tslk_level l)
      | Expr.CellAt (m,a)         -> TSLK.CellAt (mem_to_tslk_mem m, addr_to_tslk_addr a)
      | Expr.CellArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarCell (variable_to_tslk_var v)
      | Expr.CellArrayRd _        -> raise(UnsupportedTSLKExpr(Expr.cell_to_str c))


    and setth_to_tslk_setth (st:Expr.setth) : TSLK.setth =
      let to_setth = setth_to_tslk_setth in
      match st with
        Expr.VarSetTh v        -> TSLK.VarSetTh (variable_to_tslk_var v)
      | Expr.EmptySetTh        -> TSLK.EmptySetTh
      | Expr.SinglTh t         -> TSLK.SinglTh (tid_to_tslk_tid t)
      | Expr.UnionTh (s1,s2)   -> TSLK.UnionTh (to_setth s1, to_setth s2)
      | Expr.IntrTh (s1,s2)    -> TSLK.IntrTh (to_setth s1, to_setth s2)
      | Expr.SetdiffTh (s1,s2) -> TSLK.SetdiffTh (to_setth s1, to_setth s2)
      | Expr.SetThArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSetTh (variable_to_tslk_var v)
      | Expr.SetThArrayRd _    -> raise(UnsupportedTSLKExpr
                                                (Expr.setth_to_str st))


    and setelem_to_tslk_setelem (st:Expr.setelem) : TSLK.setelem =
      let to_setelem = setelem_to_tslk_setelem in
      match st with
        Expr.VarSetElem v        -> TSLK.VarSetElem (variable_to_tslk_var v)
      | Expr.EmptySetElem        -> TSLK.EmptySetElem
      | Expr.SinglElem e         -> TSLK.SinglElem (elem_to_tslk_elem e)
      | Expr.UnionElem (s1,s2)   -> TSLK.UnionElem (to_setelem s1, to_setelem s2)
      | Expr.IntrElem (s1,s2)    -> TSLK.IntrElem (to_setelem s1, to_setelem s2)
      | Expr.SetdiffElem (s1,s2) -> TSLK.SetdiffElem (to_setelem s1, to_setelem s2)
      | Expr.SetElemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarSetElem (variable_to_tslk_var v)
      | Expr.SetToElems (s,m)    -> TSLK.SetToElems (set_to_tslk_set s,
                                                    mem_to_tslk_mem m)
      | Expr.SetElemArrayRd _    -> raise(UnsupportedTSLKExpr
                                                (Expr.setelem_to_str st))


    and path_to_tslk_path (p:Expr.path) : TSLK.path =
      match p with
        Expr.VarPath v             -> TSLK.VarPath (variable_to_tslk_var v)
      | Expr.Epsilon               -> TSLK.Epsilon
      | Expr.SimplePath a          -> TSLK.SimplePath (addr_to_tslk_addr a)
      | Expr.GetPath _             -> raise(UnsupportedTSLKExpr(Expr.path_to_str p))
      | Expr.GetPathAt (m,a1,a2,l) -> TSLK.GetPathAt (mem_to_tslk_mem m,
                                                      addr_to_tslk_addr a1,
                                                      addr_to_tslk_addr a2,
                                                      int_to_tslk_level l)
      | Expr.PathArrayRd _         -> raise(UnsupportedTSLKExpr(Expr.path_to_str p))


    and mem_to_tslk_mem (m:Expr.mem) : TSLK.mem =
      match m with
        Expr.VarMem v       -> TSLK.VarMem (variable_to_tslk_var v)
      | Expr.Update (m,a,c) -> TSLK.Update (mem_to_tslk_mem m,
                                           addr_to_tslk_addr a,
                                           cell_to_tslk_cell c)
      (* Missing the case for "emp" *)
      | Expr.MemArrayRd (Expr.VarArray (id,s,pr,th,p,_),t) ->
          let v = Expr.build_var id s pr (Some t) p Expr.Normal in
          TSLK.VarMem (variable_to_tslk_var v)
      | Expr.MemArrayRd _        -> raise (UnsupportedTSLKExpr (Expr.mem_to_str m))


    and int_to_tslk_level (i:Expr.integer) : TSLK.level =
      let rec apply n f x = if n <= 1 then f x else apply (n-1) f (f x) in
      let succ = (fun x -> TSLK.LevelSucc x) in
      let pred = (fun x -> TSLK.LevelPred x) in
      let tolevel = int_to_tslk_level in
      match i with
        Expr.IntVal l       -> if l < 0 || TSLK.k <= l then
                                 begin
                                   Interface.Err.msg "Level out of bounds" $
                                   Printf.sprintf "Level %i is out of the bounds of TSLK[%i], \
                                                   which goes from 0 to %i."
                                      l TSLK.k (TSLK.k-1);
                                   raise (UnsupportedTSLKExpr(Expr.integer_to_str i))
                                 end
                               else
                                 TSLK.LevelVal l
      | Expr.VarInt v       -> TSLK.VarLevel (variable_to_tslk_var v)
      | Expr.IntNeg i       -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntAdd (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (Expr.IntVal j1, Expr.IntVal j2) -> TSLK.LevelVal (j1+j2)
                                 | (Expr.VarInt v , Expr.IntVal j ) -> apply j succ (tolevel i1)
                                 | (Expr.IntVal j , Expr.VarInt v ) -> apply j succ (tolevel i2)
                                 | _ -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
                               end
      | Expr.IntSub (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (Expr.IntVal j1, Expr.IntVal j2) -> TSLK.LevelVal (j1-j2)
                                 | (Expr.VarInt v , Expr.IntVal j ) -> apply j pred (tolevel i1)
                                 | _ -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
                               end
      | Expr.IntMul (i1,i2) -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntDiv (i1,i2) -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.CellMax (c)    -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntArrayRd _   -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntSetMin _    -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.IntSetMax _    -> raise(UnsupportedTSLKExpr(Expr.integer_to_str i))
      | Expr.HavocLevel     -> TSLK.HavocLevel


    and atom_to_tslk_atom (a:Expr.atom) : TSLK.atom =
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
        Expr.Append (p1,p2,p3)    -> TSLK.Append (path p1,path p2,path p3)
      | Expr.Reach _              -> raise (UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.ReachAt (m,a1,a2,l,p)-> TSLK.Reach (mem m, addr a1, addr a2, integ l, path p)
      | Expr.OrderList(m,a1,a2)   -> TSLK.OrderList (mem m, addr a1, addr a2)
      | Expr.Skiplist _           -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.In (a,s)             -> TSLK.In (addr a, set s)
      | Expr.SubsetEq (s1,s2)     -> TSLK.SubsetEq (set s1, set s2)
      | Expr.InTh (t,s)           -> TSLK.InTh (tid t, setth s)
      | Expr.SubsetEqTh (s1,s2)   -> TSLK.SubsetEqTh (setth s1, setth s2)
      | Expr.InInt _              -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.SubsetEqInt _        -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.InElem (e,s)         -> TSLK.InElem (elem_to_tslk_elem e, setelem s)
      | Expr.SubsetEqElem (s1,s2) -> TSLK.SubsetEqElem (setelem s1, setelem s2)
      | Expr.Less (i1,i2)         -> TSLK.Less (integ i1, integ i2)
      | Expr.Greater (i1,i2)      -> TSLK.Greater (integ i1, integ i2)
      | Expr.LessEq (i1,i2)       -> TSLK.LessEq (integ i1, integ i2)
      | Expr.GreaterEq (i1,i2)    -> TSLK.GreaterEq (integ i1, integ i2)
      | Expr.LessTid _            -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.LessElem (e1,e2)     -> TSLK.LessElem (elem e1, elem e2)
      | Expr.GreaterElem (e1,e2)  -> TSLK.GreaterElem (elem e1, elem e2)
      | Expr.Eq (t1,t2)           -> TSLK.Eq (term t1, term t2)
      | Expr.InEq (t1,t2)         -> TSLK.InEq (term t1, term t2)
      | Expr.BoolVar _            -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.BoolArrayRd _        -> raise(UnsupportedTSLKExpr(Expr.atom_to_str a))
      | Expr.PC (pc,t,pr)         -> TSLK.PC (pc, Option.lift tid_to_tslk_tid t,pr)
      | Expr.PCUpdate (pc,t)      -> TSLK.PCUpdate (pc, tid_to_tslk_tid t)
      | Expr.PCRange (pc1,pc2,t,pr) -> TSLK.PCRange (pc1, pc2,
                                            Option.lift tid_to_tslk_tid t,pr)


    and literal_to_tslk_literal (l:Expr.literal) : TSLK.literal =
      match l with
        Expr.Atom a    -> TSLK.Atom (atom_to_tslk_atom a)
      | Expr.NegAtom a -> TSLK.NegAtom (atom_to_tslk_atom a)


    and formula_to_tslk_formula (f:Expr.formula) : TSLK.formula =
      let to_formula = formula_to_tslk_formula in
      match f with
        Expr.Literal l       -> TSLK.Literal (literal_to_tslk_literal l)
      | Expr.True            -> TSLK.True
      | Expr.False           -> TSLK.False
      | Expr.And (f1,f2)     -> TSLK.And (to_formula f1, to_formula f2)
      | Expr.Or (f1,f2)      -> TSLK.Or (to_formula f1, to_formula f2)
      | Expr.Not f1          -> TSLK.Not (to_formula f1)
      | Expr.Implies (f1,f2) -> TSLK.Implies (to_formula f1, to_formula f2)
      | Expr.Iff (f1,f2)     -> TSLK.Iff (to_formula f1, to_formula f2)

  end
