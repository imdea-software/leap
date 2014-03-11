open LeapLib


module E = Expression
module F = Formula

type sort =
  | Set
  | Elem
  | Tid
  | Addr
  | Cell
  | SetTh
  | SetElem
  | Path
  | Mem
  | Int
  | Bool
  | Unknown

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = unit
  end )

type logic_op_t = AndOp | OrOp | ImpliesOp | IffOp | NotOp | NoneOp

type term =
    VarT     of V.t
  | SetT     of set
  | ElemT    of elem
  | TidT     of tid
  | AddrT    of addr
  | CellT    of cell
  | SetThT   of setth
  | SetElemT of setelem
  | PathT    of path
  | MemT     of mem
  | IntT     of integer
  | VarUpdate  of V.t * tid * term
and eq = term * term
and diseq = term * term
and integer =
    IntVal        of int
  | VarInt        of V.t
  | IntNeg        of integer
  | IntAdd        of integer * integer
  | IntSub        of integer * integer
  | IntMul        of integer * integer
  | IntDiv        of integer * integer
and set =
    VarSet of V.t
  | EmptySet
  | Singl     of addr
  | Union     of set * set
  | Intr      of set * set
  | Setdiff   of set * set
  | PathToSet of path
  | AddrToSet of mem * addr
and tid =
    VarTh of V.t
  | NoTid
  | CellLockId of cell
and elem =
    VarElem of V.t
  | CellData of cell
  | HavocListElem
  | LowestElem
  | HighestElem
and addr =
    VarAddr of V.t
  | Null
  | Next of cell
  | FirstLocked of mem * path
(*  | Malloc of elem * addr * tid *)
and cell =
    VarCell of V.t
  | Error
  | MkCell of elem * addr * tid
  | CellLock of cell * tid
  | CellUnlock of cell
  | CellAt of mem * addr
and setth =
    VarSetTh of V.t
  | EmptySetTh
  | SinglTh   of tid
  | UnionTh   of setth * setth
  | IntrTh    of setth * setth
  | SetdiffTh of setth * setth
and setelem =
    VarSetElem   of V.t
  | EmptySetElem
  | SinglElem    of elem
  | UnionElem    of setelem * setelem
  | IntrElem     of setelem * setelem
  | SetToElems   of set * mem
  | SetdiffElem  of setelem * setelem
and path =
    VarPath of V.t
  | Epsilon
  | SimplePath of addr
  | GetPath    of mem * addr * addr 
and mem =
    VarMem of V.t
  | Emp
  | Update of mem * addr * cell
and atom =
    Append       of path * path * path
  | Reach        of mem * addr * addr * path
  | OrderList    of mem * addr * addr
  | In           of addr * set
  | SubsetEq     of set  * set
  | InTh         of tid * setth
  | SubsetEqTh   of setth * setth
  | InElem       of elem * setelem
  | SubsetEqElem of setelem * setelem
  | Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessElem     of elem * elem
  | GreaterElem  of elem * elem
  | Eq           of eq
  | InEq         of diseq
  | BoolVar      of V.t
  | PC           of int * V.shared_or_local * bool
  | PCUpdate     of int * tid
  | PCRange      of int * int * V.shared_or_local * bool

and literal = atom F.literal

and conjunctive_formula = atom F.conjunctive_formula

and formula = atom F.formula

type special_op_t =
  | Reachable
  | Addr2Set
  | Path2Set
  | FstLocked
  | Getp
  | Set2Elem
  | ElemOrder
  | OrderedList

exception WrongType of term
exception Not_tid_var of tid
exception UnsupportedSort of string
exception UnsupportedTllExpr of string



(*************************)
(* VARIABLE MANIPULATION *)
(*************************)

let build_var ?(fresh=false)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id s pr th p () ~fresh:fresh


let is_primed_tid (th:tid) : bool =
  match th with
  | VarTh v           -> V.is_primed v
  | NoTid             -> false
  | CellLockId _      -> false
  (* FIX: Propagate the query inside cell??? *)


(*******************************)
(* VARLIST/VARSET FOR FORMULAS *)
(*******************************)

module AtomSet = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = atom
  end
)

module SortSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = sort
  end )


module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )


module OpsSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = special_op_t
  end )

(*
module LiteralSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = literal
  end )
*)


module TermSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = term
  end )



(**********  Folding  ***************)

type ('info, 'a) fold_ops_t =
  {
    base : 'info -> 'a;
    concat : 'a -> 'a -> 'a;
    var_f : ('info,'a) fold_ops_t -> 'info -> V.t -> 'a;
    mutable addr_f : ('info,'a) fold_ops_t -> 'info -> addr -> 'a;
    mutable elem_f : ('info,'a) fold_ops_t -> 'info -> elem -> 'a;
    mutable tid_f : ('info,'a) fold_ops_t -> 'info -> tid -> 'a;
    mutable int_f : ('info,'a) fold_ops_t -> 'info -> integer -> 'a;
    mutable cell_f : ('info,'a) fold_ops_t -> 'info -> cell -> 'a;
    mutable mem_f : ('info,'a) fold_ops_t -> 'info -> mem -> 'a;
    mutable path_f : ('info,'a) fold_ops_t -> 'info -> path -> 'a;
    mutable set_f : ('info,'a) fold_ops_t -> 'info -> set -> 'a;
    mutable setelem_f : ('info,'a) fold_ops_t -> 'info -> setelem -> 'a;
    mutable setth_f : ('info,'a) fold_ops_t -> 'info -> setth -> 'a;
    mutable atom_f : ('info,'a) fold_ops_t -> 'info -> atom -> 'a;
    mutable term_f : ('info,'a) fold_ops_t -> 'info -> term -> 'a;
  }

type ('info, 'a) folding_t =
  {
    var_f : 'info -> V.t -> 'a;
    addr_f : 'info -> addr -> 'a;
    elem_f : 'info -> elem -> 'a;
    tid_f : 'info -> tid -> 'a;
    int_f : 'info -> integer -> 'a;
    cell_f : 'info -> cell -> 'a;
    mem_f : 'info -> mem -> 'a;
    path_f : 'info -> path -> 'a;
    set_f : 'info -> set -> 'a;
    setelem_f : 'info -> setelem -> 'a;
    setth_f : 'info -> setth -> 'a;
    atom_f : 'info -> atom -> 'a;
    term_f : 'info -> term -> 'a;
  }



let rec fold_addr (fs:('info,'a) fold_ops_t) (info:'info) (a:addr) : 'a =
  match a with
  | VarAddr v        -> fs.var_f fs info v
  | Null             -> fs.base info
  | Next c           -> fs.cell_f fs info c
  | FirstLocked(m,p) -> fs.concat (fs.mem_f fs info m) (fs.path_f fs info p)

and fold_elem (fs:('info,'a) fold_ops_t) (info:'info) (e:elem) : 'a =
  match e with
  | VarElem v     -> fs.var_f fs info v
  | CellData c    -> fs.cell_f fs info c
  | HavocListElem -> fs.base info
  | LowestElem    -> fs.base info
  | HighestElem   -> fs.base info

and fold_tid (fs:('info,'a) fold_ops_t) (info:'info) (t:tid) : 'a =
  match t with
  | VarTh v      -> fs.var_f fs info v
  | NoTid        -> fs.base info
  | CellLockId c -> fs.cell_f fs info c

and fold_int (fs:('info,'a) fold_ops_t) (info:'info) (i:integer) : 'a =
  match i with
  | IntVal _ -> fs.base info
  | VarInt v -> fs.var_f fs info v
  | IntNeg j -> fs.int_f fs info j
  | IntAdd (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntSub (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntMul (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntDiv (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)

and fold_cell (fs:('info,'a) fold_ops_t) (info:'info) (c:cell) : 'a =
  match c with
  | VarCell v      -> fs.var_f fs info v
  | Error          -> fs.base info
  | MkCell(e,a,th) -> fs.concat (fs.elem_f fs info e)
                                (fs.concat (fs.addr_f fs info a)
                                           (fs.tid_f fs info th))
  | CellLock(c,th) -> fs.concat (fs.cell_f fs info c) (fs.tid_f fs info th)
  | CellUnlock(c)  -> fs.cell_f fs info c
  | CellAt(m,a)    -> fs.concat (fs.mem_f fs info m) (fs.addr_f fs info a)

and fold_mem (fs:('info,'a) fold_ops_t) (info:'info) (m:mem) : 'a =
  match m with
  | VarMem v      -> fs.var_f fs info v
  | Emp           -> fs.base info
  | Update(m,a,c) -> fs.concat (fs.mem_f fs info m)
                               (fs.concat (fs.addr_f fs info a)
                                          (fs.cell_f fs info c))

and fold_path (fs:('info,'a) fold_ops_t) (info:'info) (p:path) : 'a =
  match p with
  | VarPath v        -> fs.var_f fs info v
  | Epsilon          -> fs.base info
  | SimplePath(a)    -> fs.addr_f fs info a
  | GetPath(m,a1,a2) -> fs.concat (fs.mem_f fs info m)
                                  (fs.concat (fs.addr_f fs info a1)
                                             (fs.addr_f fs info a2))

and fold_set (fs:('info,'a) fold_ops_t) (info:'info) (s:set) : 'a =
  match s with
  | VarSet v       -> fs.var_f fs info v
  | EmptySet       -> fs.base info
  | Singl(a)       -> fs.addr_f fs info a
  | Union(s1,s2)   -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Intr(s1,s2)    -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Setdiff(s1,s2) -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | PathToSet(p)   -> fs.path_f fs info p
  | AddrToSet(m,a) -> fs.concat (fs.mem_f fs info m) (fs.addr_f fs info a)

and fold_setelem (fs:('info,'a) fold_ops_t) (info:'info) (se:setelem) : 'a =
  match se with
  | VarSetElem v         -> fs.var_f fs info v
  | EmptySetElem         -> fs.base info
  | SinglElem(e)         -> fs.elem_f fs info e
  | UnionElem(st1,st2)   -> fs.concat (fs.setelem_f fs info st1)
                                      (fs.setelem_f fs info st2)
  | IntrElem(st1,st2)    -> fs.concat (fs.setelem_f fs info st1)
                                      (fs.setelem_f fs info st2)
  | SetToElems(s,m)      -> fs.concat (fs.set_f fs info s) (fs.mem_f fs info m)
  | SetdiffElem(st1,st2) -> fs.concat (fs.setelem_f fs info st1)
                                      (fs.setelem_f fs info st2)

and fold_setth (fs:('info,'a) fold_ops_t) (info:'info) (sth:setth) : 'a =
  match sth with
  | VarSetTh v         -> fs.var_f fs info v
  | EmptySetTh         -> fs.base info
  | SinglTh(th)        -> fs.tid_f fs info th
  | UnionTh(st1,st2)   -> fs.concat (fs.setth_f fs info st1) (fs.setth_f fs info st2)
  | IntrTh(st1,st2)    -> fs.concat (fs.setth_f fs info st1) (fs.setth_f fs info st2)
  | SetdiffTh(st1,st2) -> fs.concat (fs.setth_f fs info st1) (fs.setth_f fs info st2)

and fold_atom (fs:('info,'a) fold_ops_t) (info:'info) (a:atom) : 'a =
  match a with
  | Append(p1,p2,p3)       -> fs.concat (fs.path_f fs info p1)
                                        (fs.concat (fs.path_f fs info p2)
                                                   (fs.path_f fs info p3))
  | Reach(m,a1,a2,p)       -> fs.concat (fs.mem_f fs info m)
                                        (fs.concat (fs.addr_f fs info a1)
                                                   (fs.concat (fs.addr_f fs info a2)
                                                              (fs.path_f fs info p)))
  | OrderList(m,a1,a2)     -> fs.concat (fs.mem_f fs info m)
                                        (fs.concat (fs.addr_f fs info a1)
                                                   (fs.addr_f fs info a2))
  | In(a,s)                -> fs.concat (fs.addr_f fs info a) (fs.set_f fs info s)
  | SubsetEq(s1,s2)        -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | InTh(th,st)            -> fs.concat (fs.tid_f fs info th) (fs.setth_f fs info st)
  | SubsetEqTh(st1,st2)    -> fs.concat (fs.setth_f fs info st1)
                                        (fs.setth_f fs info st2)
  | InElem(e,se)           -> fs.concat (fs.elem_f fs info e) (fs.setelem_f fs info se)
  | SubsetEqElem(se1,se2)  -> fs.concat (fs.setelem_f fs info se1)
                                        (fs.setelem_f fs info se2)
  | Less(i1,i2)            -> fs.concat (fs.int_f fs info i1) (fs.int_f fs info i2)
  | LessEq(i1,i2)          -> fs.concat (fs.int_f fs info i1) (fs.int_f fs info i2)
  | Greater(i1,i2)         -> fs.concat (fs.int_f fs info i1) (fs.int_f fs info i2)
  | GreaterEq(i1,i2)       -> fs.concat (fs.int_f fs info i1) (fs.int_f fs info i2)
  | LessElem(e1,e2)        -> fs.concat (fs.elem_f fs info e1) (fs.elem_f fs info e2)
  | GreaterElem(e1,e2)     -> fs.concat (fs.elem_f fs info e1) (fs.elem_f fs info e2)
  | Eq((x,y))              -> fs.concat (fs.term_f fs info x) (fs.term_f fs info y)
  | InEq((x,y))            -> fs.concat (fs.term_f fs info x) (fs.term_f fs info y)
  | BoolVar v              -> fs.var_f fs info v
  | PC(pc,th,pr)           -> (match th with
                               | V.Shared -> fs.base info
                               | V.Local t -> fs.var_f fs info t)
  | PCUpdate (pc,th)       -> fs.tid_f fs info th
  | PCRange(pc1,pc2,th,pr) -> (match th with
                               | V.Shared -> fs.base info
                               | V.Local t -> fs.var_f fs info t)

and fold_term (fs:('info,'a) fold_ops_t) (info:'info) (t:term) : 'a =
  match t with
  | VarT   v          -> fs.var_f fs info v
  | SetT   s          -> fs.set_f fs info s
  | ElemT  e          -> fs.elem_f fs info e
  | TidT  th          -> fs.tid_f fs info th
  | AddrT  a          -> fs.addr_f fs info a
  | CellT  c          -> fs.cell_f fs info c
  | SetThT st         -> fs.setth_f fs info st
  | SetElemT se       -> fs.setelem_f fs info se
  | PathT  p          -> fs.path_f fs info p
  | MemT   m          -> fs.mem_f fs info m
  | IntT   i          -> fs.int_f fs info i
  | VarUpdate(v,pc,t) -> fs.concat (fs.var_f fs info v)
                                   (fs.concat (fs.tid_f fs info pc)
                                              (fs.term_f fs info t))



let make_fold ?(addr_f=fold_addr)
              ?(elem_f=fold_elem)
              ?(tid_f=fold_tid)
              ?(int_f=fold_int)
              ?(cell_f=fold_cell)
              ?(mem_f=fold_mem)
              ?(path_f=fold_path)
              ?(set_f=fold_set)
              ?(setelem_f=fold_setelem)
              ?(setth_f=fold_setth)
              ?(atom_f=fold_atom)
              ?(term_f=fold_term)
              (base:('info -> 'a))
              (concat:('a -> 'a -> 'a))
              (var_f :(('info,'a) fold_ops_t -> 'info -> V.t -> 'a))
    : ('info,'a) folding_t =
  let fs : ('info,'a) fold_ops_t = {
    addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
    int_f = int_f; cell_f = cell_f; mem_f = mem_f;
    path_f = path_f; set_f = set_f; setelem_f = setelem_f;
    setth_f = setth_f; atom_f = atom_f; term_f = term_f;
    base = base; concat = concat; var_f = var_f; } in
  { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
    int_f = int_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
    path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
    setth_f = setth_f fs; atom_f = atom_f fs; term_f = term_f fs;
    var_f = var_f fs; }


(**********  Mapping  ***************)

type 'info map_ops_t =
  {
    var_f : ('info map_ops_t) -> 'info -> V.t -> V.t;
    mutable addr_f : 'info map_ops_t -> 'info -> addr -> addr;
    mutable elem_f : 'info map_ops_t -> 'info -> elem -> elem;
    mutable tid_f : 'info map_ops_t -> 'info -> tid -> tid;
    mutable int_f : 'info map_ops_t -> 'info -> integer -> integer;
    mutable cell_f : 'info map_ops_t -> 'info -> cell -> cell;
    mutable mem_f : 'info map_ops_t -> 'info -> mem -> mem;
    mutable path_f : 'info map_ops_t -> 'info -> path -> path;
    mutable set_f : 'info map_ops_t -> 'info -> set -> set;
    mutable setelem_f : 'info map_ops_t -> 'info -> setelem -> setelem;
    mutable setth_f : 'info map_ops_t -> 'info -> setth ->setth;
    mutable atom_f : 'info map_ops_t -> 'info -> atom -> atom;
    mutable term_f : 'info map_ops_t -> 'info -> term -> term;
  }

type 'info mapping_t =
  {
    var_f : 'info -> V.t -> V.t;
    addr_f : 'info -> addr -> addr;
    elem_f : 'info -> elem -> elem;
    tid_f : 'info -> tid -> tid;
    int_f : 'info -> integer -> integer;
    cell_f : 'info -> cell -> cell;
    mem_f : 'info -> mem -> mem;
    path_f : 'info -> path -> path;
    set_f : 'info -> set -> set;
    setelem_f : 'info -> setelem -> setelem;
    setth_f : 'info -> setth -> setth;
    atom_f : 'info -> atom -> atom;
    term_f : 'info -> term -> term;
  }



let rec map_addr (fs:'info map_ops_t) (info:'info) (a:addr) : addr =
  match a with
  | VarAddr v        -> VarAddr (fs.var_f fs info v)
  | Null             -> Null
  | Next c           -> Next (fs.cell_f fs info c)
  | FirstLocked(m,p) -> FirstLocked(fs.mem_f fs info m, fs.path_f fs info p)

and map_elem (fs:'info map_ops_t) (info:'info) (e:elem) : elem =
  match e with
  | VarElem v     -> VarElem (fs.var_f fs info v)
  | CellData c    -> CellData (fs.cell_f fs info c)
  | HavocListElem -> HavocListElem
  | LowestElem    -> LowestElem
  | HighestElem   -> HighestElem

and map_tid (fs:'info map_ops_t) (info:'info) (t:tid) : tid =
  match t with
  | VarTh v      -> VarTh (fs.var_f fs info v)
  | NoTid        -> NoTid
  | CellLockId c -> CellLockId (fs.cell_f fs info c)

and map_int (fs:'info map_ops_t) (info:'info) (i:integer) : integer =
  match i with
  | IntVal j -> IntVal j
  | VarInt v -> VarInt (fs.var_f fs info v)
  | IntNeg j -> IntNeg (fs.int_f fs info j)
  | IntAdd (j1,j2) -> IntAdd (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntSub (j1,j2) -> IntSub (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntMul (j1,j2) -> IntMul (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntDiv (j1,j2) -> IntDiv (fs.int_f fs info j1, fs.int_f fs info j2)

and map_cell (fs:'info map_ops_t) (info:'info) (c:cell) : cell =
  match c with
  | VarCell v      -> VarCell (fs.var_f fs info v)
  | Error          -> Error
  | MkCell(e,a,th) -> MkCell(fs.elem_f fs info e,
                             fs.addr_f fs info a,
                             fs.tid_f fs info th)
  | CellLock(c,th) -> CellLock (fs.cell_f fs info c, fs.tid_f fs info th)
  | CellUnlock(c)  -> CellUnlock (fs.cell_f fs info c)
  | CellAt(m,a)    -> CellAt (fs.mem_f fs info m, fs.addr_f fs info a)

and map_mem (fs:'info map_ops_t) (info:'info) (m:mem) : mem =
  match m with
  | VarMem v      -> VarMem (fs.var_f fs info v)
  | Emp           -> Emp
  | Update(m,a,c) -> Update (fs.mem_f fs info m,
                             fs.addr_f fs info a,
                             fs.cell_f fs info c)

and map_path (fs:'info map_ops_t) (info:'info) (p:path) : path =
  match p with
  | VarPath v        -> VarPath (fs.var_f fs info v)
  | Epsilon          -> Epsilon
  | SimplePath(a)    -> SimplePath (fs.addr_f fs info a)
  | GetPath(m,a1,a2) -> GetPath (fs.mem_f fs info m,
                                 fs.addr_f fs info a1,
                                 fs.addr_f fs info a2)

and map_set (fs:'info map_ops_t) (info:'info) (s:set) : set =
  match s with
  | VarSet v       -> VarSet (fs.var_f fs info v)
  | EmptySet       -> EmptySet
  | Singl(a)       -> Singl (fs.addr_f fs info a)
  | Union(s1,s2)   -> Union (fs.set_f fs info s1, fs.set_f fs info s2)
  | Intr(s1,s2)    -> Intr (fs.set_f fs info s1, fs.set_f fs info s2)
  | Setdiff(s1,s2) -> Setdiff (fs.set_f fs info s1, fs.set_f fs info s2)
  | PathToSet(p)   -> PathToSet (fs.path_f fs info p)
  | AddrToSet(m,a) -> AddrToSet (fs.mem_f fs info m, fs.addr_f fs info a)

and map_setelem (fs:'info map_ops_t) (info:'info) (se:setelem) : setelem =
  match se with
  | VarSetElem v         -> VarSetElem (fs.var_f fs info v)
  | EmptySetElem         -> EmptySetElem
  | SinglElem(e)         -> SinglElem (fs.elem_f fs info e)
  | UnionElem(st1,st2)   -> UnionElem (fs.setelem_f fs info st1,
                                       fs.setelem_f fs info st2)
  | IntrElem(st1,st2)    -> IntrElem (fs.setelem_f fs info st1,
                                      fs.setelem_f fs info st2)
  | SetToElems(s,m)      -> SetToElems (fs.set_f fs info s, fs.mem_f fs info m)
  | SetdiffElem(st1,st2) -> SetdiffElem (fs.setelem_f fs info st1,
                                         fs.setelem_f fs info st2)

and map_setth (fs:'info map_ops_t) (info:'info) (sth:setth) : setth =
  match sth with
  | VarSetTh v         -> VarSetTh (fs.var_f fs info v)
  | EmptySetTh         -> EmptySetTh
  | SinglTh(th)        -> SinglTh (fs.tid_f fs info th)
  | UnionTh(st1,st2)   -> UnionTh (fs.setth_f fs info st1,
                                   fs.setth_f fs info st2)
  | IntrTh(st1,st2)    -> IntrTh (fs.setth_f fs info st1,
                                  fs.setth_f fs info st2)
  | SetdiffTh(st1,st2) -> SetdiffTh (fs.setth_f fs info st1,
                                     fs.setth_f fs info st2)

and map_atom (fs:'info map_ops_t) (info:'info) (a:atom) : atom =
  match a with
  | Append(p1,p2,p3)       -> Append (fs.path_f fs info p1,
                                      fs.path_f fs info p2,
                                      fs.path_f fs info p3)
  | Reach(m,a1,a2,p)       -> Reach (fs.mem_f fs info m,
                                     fs.addr_f fs info a1,
                                     fs.addr_f fs info a2,
                                     fs.path_f fs info p)
  | OrderList(m,a1,a2)     -> OrderList (fs.mem_f fs info m,
                                         fs.addr_f fs info a1,
                                         fs.addr_f fs info a2)
  | In(a,s)                -> In (fs.addr_f fs info a, fs.set_f fs info s)
  | SubsetEq(s1,s2)        -> SubsetEq (fs.set_f fs info s1,
                                        fs.set_f fs info s2)
  | InTh(th,st)            -> InTh (fs.tid_f fs info th, fs.setth_f fs info st)
  | SubsetEqTh(st1,st2)    -> SubsetEqTh (fs.setth_f fs info st1,
                                          fs.setth_f fs info st2)
  | InElem(e,se)           -> InElem (fs.elem_f fs info e,
                                      fs.setelem_f fs info se)
  | SubsetEqElem(se1,se2)  -> SubsetEqElem (fs.setelem_f fs info se1,
                                            fs.setelem_f fs info se2)
  | Less(i1,i2)            -> Less (fs.int_f fs info i1, fs.int_f fs info i2)
  | LessEq(i1,i2)          -> LessEq (fs.int_f fs info i1, fs.int_f fs info i2)
  | Greater(i1,i2)         -> Greater (fs.int_f fs info i1, fs.int_f fs info i2)
  | GreaterEq(i1,i2)       -> GreaterEq (fs.int_f fs info i1,
                                         fs.int_f fs info i2)
  | LessElem(e1,e2)        -> LessElem (fs.elem_f fs info e1,
                                        fs.elem_f fs info e2)
  | GreaterElem(e1,e2)     -> GreaterElem (fs.elem_f fs info e1,
                                           fs.elem_f fs info e2)
  | Eq((x,y))              -> Eq (fs.term_f fs info x, fs.term_f fs info y)
  | InEq((x,y))            -> InEq (fs.term_f fs info x, fs.term_f fs info y)
  | BoolVar v              -> BoolVar (fs.var_f fs info v)
  | PC(pc,th,pr)           -> PC(pc, (match th with
                                      | V.Shared -> V.Shared
                                      | V.Local t -> V.Local(fs.var_f fs info t)),
                                 pr)
  | PCUpdate (pc,th)       -> PCUpdate (pc, fs.tid_f fs info th)
  | PCRange(pc1,pc2,th,pr) -> PCRange (pc1, pc2,
                                       (match th with
                                        | V.Shared -> V.Shared
                                        | V.Local t -> V.Local(fs.var_f fs info t)),
                                       pr)

and map_term (fs:'info map_ops_t) (info:'info) (t:term) : term =
  match t with
  | VarT   v          -> VarT (fs.var_f fs info v)
  | SetT   s          -> SetT (fs.set_f fs info s)
  | ElemT  e          -> ElemT (fs.elem_f fs info e)
  | TidT  th          -> TidT (fs.tid_f fs info th)
  | AddrT  a          -> AddrT (fs.addr_f fs info a)
  | CellT  c          -> CellT (fs.cell_f fs info c)
  | SetThT st         -> SetThT (fs.setth_f fs info st)
  | SetElemT se       -> SetElemT (fs.setelem_f fs info se)
  | PathT  p          -> PathT (fs.path_f fs info p)
  | MemT   m          -> MemT (fs.mem_f fs info m)
  | IntT   i          -> IntT (fs.int_f fs info i)
  | VarUpdate(v,pc,t) -> VarUpdate (fs.var_f fs info v,
                                    fs.tid_f fs info pc,
                                    fs.term_f fs info t)



let make_map ?(addr_f=map_addr)
             ?(elem_f=map_elem)
             ?(tid_f=map_tid)
             ?(int_f=map_int)
             ?(cell_f=map_cell)
             ?(mem_f=map_mem)
             ?(path_f=map_path)
             ?(set_f=map_set)
             ?(setelem_f=map_setelem)
             ?(setth_f=map_setth)
             ?(atom_f=map_atom)
             ?(term_f=map_term)
              (var_f :(('info map_ops_t) -> 'info -> V.t -> V.t))
    : 'info mapping_t =
  let fs : 'info map_ops_t = {
    addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
    int_f = int_f; cell_f = cell_f; mem_f = mem_f;
    path_f = path_f; set_f = set_f; setelem_f = setelem_f;
    setth_f = setth_f; atom_f = atom_f; term_f = term_f;
    var_f = var_f; } in
  { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
    int_f = int_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
    path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
    setth_f = setth_f fs; atom_f = atom_f fs; term_f = term_f fs;
    var_f = var_f fs; }





(* Set of variables *)

let get_varset_from_param (v:V.t) : V.VarSet.t =
  match V.parameter v with
  | V.Local t -> V.VarSet.singleton t
  | _ -> V.VarSet.empty

let varset_fold =
  make_fold (fun _ -> V.VarSet.empty) V.VarSet.union
            (fun _ _ v -> V.VarSet.union (V.VarSet.singleton v) (get_varset_from_param v))


let varset_fs = F.make_fold
                  F.GenericLiteralFold
                  (varset_fold.atom_f)
                  (fun info -> V.VarSet.empty)
                  V.VarSet.union


let get_varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
  F.conjunctive_formula_fold varset_fs () cf

let get_varset_from_formula (phi:formula) : V.VarSet.t =
  F.formula_fold varset_fs () phi


let get_varset_of_sort_from_conj phi s =
  V.varset_of_sort (get_varset_from_conj phi) s


let get_varlist_from_conj phi =
  V.VarSet.elements (get_varset_from_conj phi)

let varlist_of_sort varlist s =
  let is_s v = ((V.sort v) = s) in
  List.map (fun v -> (V.localize_with_underscore (V.id v) (V.scope v)))
           (List.filter is_s varlist)

let get_varlist_of_sort_from_conj phi s =
  varlist_of_sort (get_varlist_from_conj phi) s


let rec get_termset_atom (a:atom) : TermSet.t =
  let add_list = List.fold_left (fun s e -> TermSet.add e s) TermSet.empty in
  match a with
  | Append(p1,p2,p3)       -> add_list [PathT p1; PathT p2; PathT p3]
  | Reach(m,a1,a2,p)       -> add_list [MemT m; AddrT a1; AddrT a2; PathT p]
  | OrderList(m,a1,a2)     -> add_list [MemT m; AddrT a1; AddrT a2]
  | In(a,s)                -> add_list [AddrT a; SetT s]
  | SubsetEq(s1,s2)        -> add_list [SetT s1; SetT s2]
  | InTh(th,st)            -> add_list [TidT th; SetThT st]
  | SubsetEqTh(st1,st2)    -> add_list [SetThT st1; SetThT st2]
  | InElem(e,se)           -> add_list [ElemT e; SetElemT se]
  | SubsetEqElem(se1,se2)  -> add_list [SetElemT se1; SetElemT se2]
  | Less(i1,i2)            -> add_list [IntT i1; IntT i2]
  | LessEq(i1,i2)          -> add_list [IntT i1; IntT i2]
  | Greater(i1,i2)         -> add_list [IntT i1; IntT i2]
  | GreaterEq(i1,i2)       -> add_list [IntT i1; IntT i2]
  | LessElem(e1,e2)        -> add_list [ElemT e1; ElemT e2]
  | GreaterElem(e1,e2)     -> add_list [ElemT e1; ElemT e2]
  | Eq((x,y))              -> add_list [x;y]
  | InEq((x,y))            -> add_list [x;y]
  | BoolVar v              -> add_list [VarT v]
  | PC(pc,th,pr)           -> (match th with
                               | V.Shared  -> TermSet.empty
                               | V.Local t -> add_list [TidT (VarTh t)])
  | PCUpdate (pc,th)       -> add_list [TidT th]
  | PCRange(pc1,pc2,th,pr) -> (match th with
                               | V.Shared  -> TermSet.empty
                               | V.Local t -> add_list [TidT (VarTh t)])

let termset_fs = F.make_fold
                    F.GenericLiteralFold
                    (fun info a -> get_termset_atom a)
                    (fun info -> TermSet.empty)
                    TermSet.union

let get_termset_from_conjformula (cf:conjunctive_formula) : TermSet.t =
  F.conjunctive_formula_fold termset_fs () cf

let get_termset_from_formula (phi:formula) : TermSet.t =
  F.formula_fold termset_fs () phi


let termset_of_sort (all:TermSet.t) (s:sort) : TermSet.t =
  let match_sort (t:term) : bool =
    match s with
    | Set     -> (match t with | SetT _     -> true | _ -> false)
    | Elem    -> (match t with | ElemT _    -> true | _ -> false)
    | Tid     -> (match t with | TidT _     -> true | _ -> false)
    | Addr    -> (match t with | AddrT _    -> true | _ -> false)
    | Cell    -> (match t with | CellT _    -> true | _ -> false)
    | SetTh   -> (match t with | SetThT _   -> true | _ -> false)
    | SetElem -> (match t with | SetElemT _ -> true | _ -> false)
    | Path    -> (match t with | PathT _    -> true | _ -> false)
    | Mem     -> (match t with | MemT _     -> true | _ -> false)
    | Int     -> (match t with | IntT _     -> true | _ -> false)
    | Bool    -> (match t with
                  | VarT v -> (V.sort v) = Bool
                  | _      -> false)
    | Unknown -> false in
  TermSet.fold (fun t set ->
    if match_sort t then
      TermSet.add t set
    else
      set
  ) all TermSet.empty


(********************)
(* TYPES COMPATIBLE *)
(********************)


let is_flat_fold =
  make_fold (fun _ -> true) (&&) (fun _ _ _ -> true)
  ~atom_f:(fun fs info a -> match a with
                            | BoolVar _
                            | PC _
                            | PCUpdate _
                            | PCRange _ -> true
                            | _ -> fold_atom fs info a)


let is_flat_fs = F.make_fold
                   F.GenericLiteralFold
                   (is_flat_fold.atom_f)
                   (fun info -> false)
                   (&&)

let is_literal_flat (l:literal) : bool =
  F.literal_fold is_flat_fs () l


(*******************)
(* PRETTY PRINTERS *)
(* WIHOUT FOLD     *)
(*******************)

let rec atom_to_str a =
  match a with
  | Append(p1,p2,pres)         -> "append(" ^(path_to_str p1)^ "," ^
                                             (path_to_str p2)^ "," ^
                                             (path_to_str pres)^")"
  | Reach(h,add_from,add_to,p) -> "reach(" ^(mem_to_str h)^ "," ^
                                            (addr_to_str add_from)^ ", " ^
                                            (addr_to_str add_to)^ "," ^
                                            (path_to_str p)^ ")"
  | OrderList(h,a_from,a_to)   -> "orderlist(" ^(mem_to_str h)^ "," ^
                                                (addr_to_str a_from)^ "," ^
                                                (addr_to_str a_to)^ ")"
  | In(a,s)                    -> (addr_to_str a)^ " in " ^(set_to_str s)
  | SubsetEq(s_in,s_out)       -> (set_to_str s_in)^ " subseteq " ^ (set_to_str s_out)
  | InTh(th,s)                 -> (tid_to_str th)^ " inTh " ^(setth_to_str s)
  | SubsetEqTh(s_in,s_out)     -> (setth_to_str s_in)^ " subseteqTh " ^
                                  (setth_to_str s_out)
  | InElem(e,s)                -> (elem_to_str e)^ " inElem " ^(setelem_to_str s)
  | SubsetEqElem(s_in,s_out)   -> (setelem_to_str s_in)^ " subseteqElem " ^
                                  (setelem_to_str s_out)
  | Less (i1,i2)               -> (integer_to_str i1)^ " < " ^(integer_to_str i2)
  | LessEq (i1,i2)             -> (integer_to_str i1)^ " <= " ^(integer_to_str i2)
  | Greater (i1,i2)            -> (integer_to_str i1)^ " > " ^(integer_to_str i2)
  | GreaterEq (i1,i2)          -> (integer_to_str i1)^ " >= " ^(integer_to_str i2)
  | LessElem(e1,e2)            -> (elem_to_str e1)^ " < " ^(elem_to_str e2)
  | GreaterElem(e1,e2)         -> (elem_to_str e1)^ " < " ^(elem_to_str e2)
  | Eq(exp)                    -> eq_to_str (exp)
  | InEq(exp)                  -> diseq_to_str (exp)
  | BoolVar v                  -> V.to_str v
  | PC (pc,t,pr)               -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = V.shared_or_local_to_str t in
                                  pc_str^th_str^ " = " ^(string_of_int pc)
  | PCUpdate (pc,t)            -> let th_str = tid_to_str t in
                                  "pc' = pc{" ^th_str^ "<-" ^(string_of_int pc)^ "}"
  | PCRange (pc1,pc2,t,pr)     -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = V.shared_or_local_to_str t in
                                  (string_of_int pc1)^ " <= " ^
                                    pc_str^ "(" ^th_str^ ") <= "^(string_of_int pc2)

and mem_to_str expr =
  match expr with
      VarMem(v) -> V.to_str v
    | Emp -> "emp"
    | Update(mem,add,cell) -> "upd(" ^(mem_to_str mem)^ "," ^
                                      (addr_to_str add)^ "," ^
                                      (cell_to_str cell)^ ")"
and integer_to_str expr =
  match expr with
    IntVal (i)        -> string_of_int i
  | VarInt v          -> V.to_str v
  | IntNeg i          -> "-" ^ (integer_to_str i)
  | IntAdd (i1,i2)    -> (integer_to_str i1)^ " + " ^(integer_to_str i2)
  | IntSub (i1,i2)    -> (integer_to_str i1)^ " - " ^(integer_to_str i2)
  | IntMul (i1,i2)    -> (integer_to_str i1)^ " * " ^(integer_to_str i2)
  | IntDiv (i1,i2)    -> (integer_to_str i1)^ " / " ^(integer_to_str i2)
and path_to_str expr =
  match expr with
      VarPath(v) -> V.to_str v
    | Epsilon -> "epsilon"
    | SimplePath(addr) -> "[ " ^(addr_to_str addr)^ " ]"
    | GetPath(mem,add_from,add_to) -> "getp(" ^(mem_to_str mem)^ "," ^
                                               (addr_to_str add_from)^ "," ^
                                               (addr_to_str add_to)^ ")"
and set_to_str e =
  match e with
      VarSet(v)  -> V.to_str v
    | EmptySet  -> "EmptySet"
    | Singl(addr) -> "{ " ^(addr_to_str addr)^ " }"
    | Union(s1,s2) -> (set_to_str s1)^ " Union " ^(set_to_str s2)
    | Intr(s1,s2) -> (set_to_str s1)^ " Intr " ^(set_to_str s2)
    | Setdiff(s1,s2) -> (set_to_str s1)^ " SetDiff " ^ (set_to_str s2)
    | PathToSet(path) -> "path2set(" ^(path_to_str path)^ ")"
    | AddrToSet(mem,addr) -> "addr2set(" ^(mem_to_str mem)^ "," ^
                                          (addr_to_str addr)^ ")"
and setth_to_str e =
  match e with
      VarSetTh(v)  -> V.to_str v
    | EmptySetTh  -> "EmptySetTh"
    | SinglTh(th) -> "[ " ^(tid_to_str th)^ " ]"
    | UnionTh(s1,s2) -> (setth_to_str s1)^ " UnionTh " ^(setth_to_str s2)
    | IntrTh(s1,s2) -> (setth_to_str s1)^ " IntrTh " ^(setth_to_str s2)
    | SetdiffTh(s1,s2) -> (setth_to_str s1)^ " SetDiffTh " ^(setth_to_str s2)
and setelem_to_str e =
  match e with
      VarSetElem(v)  -> V.to_str v
    | EmptySetElem  -> "EmptySetElem"
    | SinglElem(e) -> "[ " ^(elem_to_str e)^ " ]"
    | UnionElem(s1,s2) -> (setelem_to_str s1)^ " UnionElem " ^(setelem_to_str s2)
    | IntrElem(s1,s2) -> (setelem_to_str s1)^ " IntrElem " ^(setelem_to_str s2)
    | SetToElems(s,m) -> "SetToElems(" ^(set_to_str s)^ "," ^(mem_to_str m)^ ")"
    | SetdiffElem(s1,s2) -> (setelem_to_str s1 )^ " SetDiffElem " ^(setelem_to_str s2)
and cell_to_str e =
  match e with
      VarCell(v) -> V.to_str v
    | Error -> "Error"
    | MkCell(data,addr,th) -> "mkcell(" ^(elem_to_str data)^ "," ^
                                         (addr_to_str addr)^ "," ^
                                         (tid_to_str th)^ ")"
    | CellLock(cell,th)   -> (cell_to_str cell)^ ".lock(" ^(tid_to_str th)^ ")"
    | CellUnlock(cell) -> (cell_to_str cell)^ ".unlock"
    | CellAt(mem,addr) -> (mem_to_str mem) ^ "[ " ^(addr_to_str addr)^ " ]"
and addr_to_str expr =
  match expr with
      VarAddr(v) -> V.to_str v
    | Null    -> "null"
    | Next(cell)           -> (cell_to_str cell)^ ".next"
    | FirstLocked(mem,path) -> "firstlocked(" ^(mem_to_str mem)^ "," ^
                                               (path_to_str path)^ ")"
and tid_to_str th =
  match th with
      VarTh(v)         -> V.to_str v
    | NoTid           -> "NoTid"
    | CellLockId(cell) -> (cell_to_str cell)^ ".lockid"
and eq_to_str expr =
  let (e1,e2) = expr in
    (term_to_str e1)^ " = " ^(term_to_str e2)
and diseq_to_str expr =
  let (e1,e2) = expr in
    (term_to_str e1)^ " != " ^(term_to_str e2)
and elem_to_str elem =
  match elem with
      VarElem(v)     -> V.to_str v
    | CellData(cell) -> (cell_to_str cell)^ ".data"
    | HavocListElem  -> "havocListElem()"
    | LowestElem     -> "lowestElem"
    | HighestElem    -> "highestElem"
and term_to_str expr =
  match expr with
      VarT(v) -> V.to_str v
    | SetT(set)          -> (set_to_str set)
    | AddrT(addr)        -> (addr_to_str addr)
    | ElemT(elem)        -> (elem_to_str elem)
    | TidT(th)          -> (tid_to_str th)
    | CellT(cell)        -> (cell_to_str cell)
    | SetThT(setth)      -> (setth_to_str setth)
    | SetElemT(setelem)  -> (setelem_to_str setelem)
    | PathT(path)        -> (path_to_str path)
    | MemT(mem)          -> (mem_to_str mem)
    | IntT(i)            -> (integer_to_str i)
    | VarUpdate (v,th,t) -> let v_str = V.to_str v in
                            let th_str = tid_to_str th in
                            let t_str = term_to_str t in
                              v_str^ "{" ^th_str^ "<-" ^t_str^ "}"



and literal_to_str (l:literal) : string =
  F.literal_to_str atom_to_str l

let conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  F.conjunctive_formula_to_str atom_to_str cf

and formula_to_str (phi:formula) : string =
  F.formula_to_str atom_to_str phi

let sort_to_str s =
  match s with
      Set     -> "Set"
    | Elem    -> "Elem"
    | Tid    -> "Tid"
    | Addr    -> "Addr"
    | Cell    -> "Cell"
    | SetTh   -> "SetTh"
    | SetElem -> "SetElem"
    | Path    -> "Path"
    | Mem     -> "Mem"
    | Int     -> "Int"
    | Bool    -> "Bool"
    | Unknown -> "Unknown"

let generic_printer aprinter x =
  Printf.printf "%s" (aprinter x)

let print_atom a =
  generic_printer atom_to_str a

let print_formula f =
  generic_printer formula_to_str f 

let print_conjunctive_formula f = 
  generic_printer conjunctive_formula_to_str f

let print_literal b =
  generic_printer literal_to_str b

let print_addr a =
  generic_printer addr_to_str a

let print_cell  c =
  generic_printer cell_to_str c

let print_elem  e =
  generic_printer elem_to_str e

let print_tid  t =
  generic_printer tid_to_str t

let print_mem   m =
  generic_printer mem_to_str m

let print_path  p =
  generic_printer path_to_str p

let print_set   s =
  generic_printer set_to_str s

let print_setth sth =
  generic_printer setth_to_str sth

let variable_list_to_str varlist =
  List.fold_left (fun v str -> str ^ v ^ "\n") "" varlist

let print_variable_list varlist =
  generic_printer variable_list_to_str varlist

let typed_variable_list_to_str tvarlist =
  let pr str (v,s) = (str ^ v ^ ": " ^ (sort_to_str s) ^ "\n") in
    List.fold_left pr "" tvarlist

let print_variable_list varlist =
  generic_printer variable_list_to_str varlist

let print_typed_variable_list tvarlist =
  generic_printer typed_variable_list_to_str tvarlist

let variable_set_to_str varset =
  V.VarIdSet.fold (fun v str -> str ^ v ^ "\n") varset ""

let typed_variable_set_to_str tvarset =
  let pr v str = (str ^ (V.id v) ^ ": " ^ (sort_to_str (V.sort v)) ^ "\n") in
    V.VarSet.fold pr tvarset ""

let print_variable_set varset =
  generic_printer variable_set_to_str varset

let print_typed_variable_set tvarset =
  generic_printer typed_variable_set_to_str tvarset



(* VOCABULARY FUNCTIONS *)

let get_tid_in (v:V.t) : ThreadSet.t =
  match V.parameter v with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


let voc_fold =
  make_fold (fun _ -> ThreadSet.empty)
            (ThreadSet.union)
            (fun _ _ v -> get_tid_in v)
  ~tid_f:(fun fs info th -> match th with
                            | VarTh v -> ThreadSet.add th (get_tid_in v)
                            | _ -> fold_tid fs info th)
  ~term_f:(fun fs info t -> match t with
                            | VarT v -> let v_set = get_tid_in v in
                                        (match (V.sort v) with
                                         | Tid -> ThreadSet.add (VarTh v) v_set
                                         | _ -> v_set)
                            | _ -> fold_term fs info t)
  ~atom_f:(fun fs info a -> match a with
                            | PC (pc,t,_) ->
                                (match t with
                                 | V.Shared -> ThreadSet.empty
                                 | V.Local x -> ThreadSet.singleton (VarTh x))
                            | PCUpdate (pc,t) -> ThreadSet.singleton t
                            | PCRange (pc1,pc2,t,_) ->
                                (match t with
                                 | V.Shared -> ThreadSet.empty
                                 | V.Local x -> ThreadSet.singleton (VarTh x))
                            | _ -> fold_atom fs info a)


let voc_term (t:term) : ThreadSet.t = voc_fold.term_f () t

let voc_fs = F.make_fold
               F.GenericLiteralFold
               (voc_fold.atom_f)
               (fun info -> ThreadSet.empty)
               (ThreadSet.union)

let voc_conjunctive_formula (cf:atom F.conjunctive_formula) : ThreadSet.t =
  F.conjunctive_formula_fold voc_fs () cf


let voc_formula (phi:atom F.formula) : ThreadSet.t =
  F.formula_fold voc_fs () phi


let voc (phi:formula) : ThreadSet.t =
  voc_formula phi



let unprimed_voc (phi:formula) : ThreadSet.t =
  ThreadSet.filter (is_primed_tid>>not) (voc phi)


(* Vocabulary to variable conversion *)
let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)



(* FORMULA MANIPULATION FUNCTIONS *)

let required_sorts (phi:formula) : sort list =
  let req_fold =
    make_fold (fun _ -> SortSet.empty) SortSet.union
              (fun _ _ _ -> SortSet.empty)
    ~atom_f:(fun fs info a ->
        match a with
        | BoolVar _ -> SortSet.singleton Bool
        | PC _
        | PCUpdate _
        | PCRange _ -> SortSet.empty
        | _ -> fold_atom fs info a)
    ~mem_f:(fun fs info m ->
        SortSet.add Mem (fold_mem fs info m))
    ~int_f:(fun fs info i ->
        SortSet.add Int (fold_int fs info i))
    ~path_f:(fun fs info p ->
        SortSet.add Path (fold_path fs info p))
    ~setth_f:(fun fs info st ->
        SortSet.add SetTh (fold_setth fs info st))
    ~setelem_f:(fun fs info se ->
        SortSet.add SetElem (fold_setelem fs info se))
    ~cell_f:(fun fs info c ->
        SortSet.add Cell (fold_cell fs info c))
    ~addr_f:(fun fs info a ->
        SortSet.add Addr (fold_addr fs info a))
    ~elem_f:(fun fs info e ->
        SortSet.add Elem (fold_elem fs info e))
    ~tid_f:(fun fs info th ->
        SortSet.add Tid (fold_tid fs info th))
    ~set_f:(fun fs info s ->
        SortSet.add Set (fold_set fs info s))
    ~term_f:(fun fs info t ->
        match t with
        | VarT v -> SortSet.singleton (V.sort v)
        | VarUpdate (v,t,tr) -> SortSet.add (V.sort v)
                                  (fs.concat (fs.tid_f fs info t)
                                             (fs.term_f fs info tr))
        | _ -> fold_term fs info t) in


  let req_fs = F.make_fold
                 F.GenericLiteralFold
                 (req_fold.atom_f)
                 (fun info -> SortSet.empty)
                 SortSet.union
  in
    SortSet.elements (F.formula_fold req_fs () phi)

 

let special_ops (phi:formula) : special_op_t list =
  let ops_fold =
    make_fold (fun _ -> OpsSet.empty) OpsSet.union
              (fun _ _ _ -> OpsSet.empty)
    ~atom_f:(fun fs info a ->
        match a with
        | Reach _ -> OpsSet.add Reachable (fold_atom fs info a)
        | OrderList _ -> OpsSet.add OrderedList (fold_atom fs info a)
        | LessElem _ -> OpsSet.add ElemOrder (fold_atom fs info a)
        | GreaterElem _ -> OpsSet.add ElemOrder (fold_atom fs info a)
        | BoolVar _
        | PC _
        | PCUpdate _
        | PCRange _ -> OpsSet.empty
        | _ -> fold_atom fs info a)
    ~path_f:(fun fs info p ->
      match p with
      | GetPath _ -> OpsSet.add Getp (fold_path fs info p)
      | _ -> fold_path fs info p)
    ~setelem_f:(fun fs info se ->
      match se with
      | SetToElems _ -> OpsSet.add Set2Elem (fold_setelem fs info se)
      | _ -> fold_setelem fs info se)
    ~addr_f:(fun fs info a ->
      match a with
      | FirstLocked _ -> OpsSet.add FstLocked (fold_addr fs info a)
      | _ -> fold_addr fs info a)
    ~set_f:(fun fs info s ->
      match s with
      | PathToSet _ -> OpsSet.add Path2Set (fold_set fs info s)
      | AddrToSet _ -> OpsSet.add Addr2Set (fold_set fs info s)
      | _ -> fold_set fs info s) in


  let ops_fs = F.make_fold
                 F.GenericLiteralFold
                 (ops_fold.atom_f)
                 (fun info -> OpsSet.empty)
                 OpsSet.union

  in
    OpsSet.elements (F.formula_fold ops_fs () phi)



(* NOTE: I am not considering the possibility of having a1=a2 \/ a1=a3 in the formula *)
let rec get_addrs_eqs (phi:formula) : ((addr*addr) list * (addr*addr) list) =
  match phi with
  | F.Literal l -> get_addrs_eqs_lit l
  | F.And (f1,f2) -> let (es1,is1) = get_addrs_eqs f1 in
                           let (es2,is2) = get_addrs_eqs f2 in
                             (es1@es2, is1@is2)
  | F.Not f -> let (es,is) = get_addrs_eqs f in (is,es)
  | _ -> ([],[])

and get_addrs_eqs_conj (cf:conjunctive_formula) : ((addr*addr) list * (addr*addr) list) =
  match cf with
  | F.TrueConj -> ([],[])
  | F.FalseConj -> ([],[])
  | F.Conj xs -> List.fold_left (fun (es,is) l ->
                         let (es',is') = get_addrs_eqs_lit l in
                         (es@es', is@is')
                       ) ([],[]) xs

and get_addrs_eqs_lit (l:literal) : ((addr*addr) list * (addr*addr) list) =
  match l with
  | F.Atom a -> get_addrs_eqs_atom a
  | F.NegAtom a -> let (es,is) = get_addrs_eqs_atom a in (is,es)

and get_addrs_eqs_atom (a:atom) : ((addr*addr) list * (addr*addr) list) =
  match a with
  | Eq (AddrT a1, AddrT a2)   -> ([(a1,a2)],[])
  | InEq (AddrT a1, AddrT a2) -> ([],[(a1,a2)])
  | _ -> ([],[])


let param_map =
  make_map (fun _ pfun v -> V.set_param v (pfun (Some v)))

let param_fs =
  F.make_trans F.GenericLiteralTrans param_map.atom_f

(* Conversion of Expression to TllExpression *)

let rec sort_to_tll_sort (s:E.sort) : sort =
  match s with
  | E.Set       -> Set
  | E.Elem      -> Elem
  | E.Tid      -> Tid
  | E.Addr      -> Addr
  | E.Cell      -> Cell
  | E.SetTh     -> SetTh
  | E.SetInt    -> raise(UnsupportedSort(E.sort_to_str s))
  | E.SetElem   -> SetElem
  | E.Path      -> Path
  | E.Mem       -> Mem
  | E.Bool      -> Bool
  | E.Int       -> Int
  | E.Array     -> raise(UnsupportedSort(E.sort_to_str s))
  | E.AddrArray -> raise(UnsupportedSort(E.sort_to_str s))
  | E.TidArray  -> raise(UnsupportedSort(E.sort_to_str s))
  | E.Unknown   -> Unknown


and build_term_var (v:E.V.t) : term =
  let tll_v = variable_to_tll_var v in
  match (E.V.sort v) with
    E.Set   -> SetT   (VarSet   tll_v)
  | E.Elem  -> ElemT  (VarElem  tll_v)
  | E.Tid  -> TidT  (VarTh    tll_v)
  | E.Addr  -> AddrT  (VarAddr  tll_v)
  | E.Cell  -> CellT  (VarCell  tll_v)
  | E.SetTh -> SetThT (VarSetTh tll_v)
  | E.Path  -> PathT  (VarPath  tll_v)
  | E.Int   -> IntT   (VarInt   tll_v)
  | E.Mem   -> MemT   (VarMem   tll_v)
  | _          -> VarT   (tll_v)



and variable_to_tll_var (v:E.V.t) : V.t =
  build_var (E.V.id v)
                (sort_to_tll_sort (E.V.sort v))
                (E.V.is_primed v)
                (shared_to_tll_shared (E.V.parameter v))
                (scope_to_tll_scope (E.V.scope v))


and shared_to_tll_shared (th:E.V.shared_or_local) : V.shared_or_local =
  match th with
  | E.V.Shared  -> V.Shared
  | E.V.Local t -> V.Local (variable_to_tll_var t)


and scope_to_tll_scope (p:E.V.procedure_name) : V.procedure_name =
  match p with
  | E.V.GlobalScope -> V.GlobalScope
  | E.V.Scope proc  -> V.Scope proc


and tid_to_tll_tid (th:E.tid) : tid =
  match th with
    E.VarTh v        -> VarTh (variable_to_tll_var v)
  | E.NoTid          -> NoTid
  | E.CellLockId c   -> CellLockId (cell_to_tll_cell c)
  | _                -> raise(UnsupportedTllExpr(E.tid_to_str th))


and term_to_tll_term (t:E.term) : term =
  match t with
    E.VarT v       -> VarT (variable_to_tll_var v)
  | E.SetT s       -> SetT (set_to_tll_set s)
  | E.ElemT e      -> ElemT (elem_to_tll_elem e)
  | E.TidT t       -> TidT (tid_to_tll_tid t)
  | E.AddrT a      -> AddrT (addr_to_tll_addr a)
  | E.CellT c      -> CellT (cell_to_tll_cell c)
  | E.SetThT st    -> SetThT (setth_to_tll_setth st)
  | E.SetElemT st  -> SetElemT (setelem_to_tll_setelem st)
  | E.PathT p      -> PathT (path_to_tll_path p)
  | E.MemT m       -> MemT (mem_to_tll_mem m)
  | E.IntT i       -> IntT (int_to_tll_int i)
  | E.ArrayT a     -> arrays_to_tll_term a
  | _              -> raise(UnsupportedTllExpr(E.term_to_str t))


and arrays_to_tll_term (a:E.arrays) : term =
  match a with
  | E.VarArray v -> build_term_var v
  | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
      let tll_v  = variable_to_tll_var v in
      let tll_th = tid_to_tll_tid th_p in
      let tll_t  = term_to_tll_term t
      in
        VarUpdate (tll_v, tll_th, tll_t)
  | E.ArrayUp (_,_,e) -> raise(UnsupportedTllExpr(E.expr_to_str e))


and eq_to_tll_eq ((t1,t2):E.eq) : eq =
  (term_to_tll_term t1, term_to_tll_term t2)


and diseq_to_tll_eq ((t1,t2):E.diseq) : diseq =
  (term_to_tll_term t1, term_to_tll_term t2)


and set_to_tll_set (s:E.set) : set =
  let to_set = set_to_tll_set in
  match s with
    E.VarSet v        -> VarSet (variable_to_tll_var v)
  | E.EmptySet        -> EmptySet
  | E.Singl a         -> Singl (addr_to_tll_addr a)
  | E.Union (s1,s2)   -> Union (to_set s1, to_set s2)
  | E.Intr (s1,s2)    -> Intr (to_set s1, to_set s2)
  | E.Setdiff (s1,s2) -> Setdiff (to_set s1, to_set s2)
  | E.PathToSet p     -> PathToSet (path_to_tll_path p)
  | E.AddrToSet (m,a) -> AddrToSet (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.SetArrayRd (E.VarArray v,t) ->
      VarSet (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | _                 -> raise(UnsupportedTllExpr(E.set_to_str s))


and elem_to_tll_elem (e:E.elem) : elem =
  match e with
    E.VarElem v              -> VarElem (variable_to_tll_var v)
  | E.CellData c             -> CellData (cell_to_tll_cell c)
  | E.ElemArrayRd (E.VarArray v,t) ->
      VarElem (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.HavocListElem          -> HavocListElem
  | E.LowestElem             -> LowestElem
  | E.HighestElem            -> HighestElem
  | _                        -> raise(UnsupportedTllExpr(E.elem_to_str e))


and addr_to_tll_addr (a:E.addr) : addr =
  match a with
    E.VarAddr v              -> VarAddr (variable_to_tll_var v)
  | E.Null                   -> Null
  | E.Next c                 -> Next (cell_to_tll_cell c)
  | E.FirstLocked (m,p)      -> FirstLocked (mem_to_tll_mem m,
                                                    path_to_tll_path p)
  | E.AddrArrayRd (E.VarArray v,t) ->
      VarAddr (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | _                        -> raise(UnsupportedTllExpr(E.addr_to_str a))


and cell_to_tll_cell (c:E.cell) : cell =
  match c with
    E.VarCell v      -> VarCell (variable_to_tll_var v)
  | E.Error          -> Error
  | E.MkCell (e,a,t) -> MkCell (elem_to_tll_elem e,
                                       addr_to_tll_addr a,
                                       tid_to_tll_tid t)
  (* Tll receives two arguments, while current epxression receives only one *)
  (* However, for the list examples, I think we will not need it *)
  | E.CellLock (c,t) -> CellLock (cell_to_tll_cell c, tid_to_tll_tid t)
  | E.CellUnlock c   -> CellUnlock (cell_to_tll_cell c)
  | E.CellAt (m,a)   -> CellAt (mem_to_tll_mem m, addr_to_tll_addr a)
  | E.CellArrayRd (E.VarArray v,t) ->
      VarCell (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | _                -> raise(UnsupportedTllExpr(E.cell_to_str c))


and setth_to_tll_setth (st:E.setth) : setth =
  let to_setth = setth_to_tll_setth in
  match st with
    E.VarSetTh v        -> VarSetTh (variable_to_tll_var v)
  | E.EmptySetTh        -> EmptySetTh
  | E.SinglTh t         -> SinglTh (tid_to_tll_tid t)
  | E.UnionTh (s1,s2)   -> UnionTh (to_setth s1, to_setth s2)
  | E.IntrTh (s1,s2)    -> IntrTh (to_setth s1, to_setth s2)
  | E.SetdiffTh (s1,s2) -> SetdiffTh (to_setth s1, to_setth s2)
  | E.SetThArrayRd (E.VarArray v,t) ->
      VarSetTh (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | _                   -> raise(UnsupportedTllExpr(E.setth_to_str st))


and setelem_to_tll_setelem (st:E.setelem) : setelem =
  let to_setelem = setelem_to_tll_setelem in
  match st with
    E.VarSetElem v        -> VarSetElem (variable_to_tll_var v)
  | E.EmptySetElem        -> EmptySetElem
  | E.SinglElem e         -> SinglElem (elem_to_tll_elem e)
  | E.UnionElem (s1,s2)   -> UnionElem (to_setelem s1, to_setelem s2)
  | E.IntrElem (s1,s2)    -> IntrElem (to_setelem s1, to_setelem s2)
  | E.SetdiffElem (s1,s2) -> SetdiffElem (to_setelem s1, to_setelem s2)
  | E.SetElemArrayRd (E.VarArray v,t) ->
      VarSetElem (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | E.SetToElems (s,m)    -> SetToElems (set_to_tll_set s,
                                                mem_to_tll_mem m)
  | _                     -> raise(UnsupportedTllExpr(E.setelem_to_str st))


and path_to_tll_path (p:E.path) : path =
  match p with
    E.VarPath v         -> VarPath (variable_to_tll_var v)
  | E.Epsilon           -> Epsilon
  | E.SimplePath a      -> SimplePath (addr_to_tll_addr a)
  | E.GetPath (m,a1,a2) -> GetPath (mem_to_tll_mem m,
                                           addr_to_tll_addr a1,
                                           addr_to_tll_addr a2)
  | _                   -> raise(UnsupportedTllExpr(E.path_to_str p))


and mem_to_tll_mem (m:E.mem) : mem =
  match m with
    E.VarMem v       -> VarMem (variable_to_tll_var v)
  | E.Update (m,a,c) -> Update (mem_to_tll_mem m,
                                       addr_to_tll_addr a,
                                       cell_to_tll_cell c)
  (* Missing the case for "emp" *)
  | E.MemArrayRd (E.VarArray v,t) ->
      VarMem (variable_to_tll_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
  | _ -> raise(UnsupportedTllExpr(E.mem_to_str m))


and int_to_tll_int (i:E.integer) : integer =
  match i with
    E.IntVal n -> IntVal n
  | E.VarInt v -> VarInt (variable_to_tll_var v)
  | E.IntNeg j -> IntNeg (int_to_tll_int j)
  | E.IntAdd (j1,j2) -> IntAdd (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntSub (j1,j2) -> IntSub (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntMul (j1,j2) -> IntMul (int_to_tll_int j1, int_to_tll_int j2)
  | E.IntDiv (j1,j2) -> IntDiv (int_to_tll_int j1, int_to_tll_int j2)
  | _                -> raise(UnsupportedTllExpr(E.integer_to_str i))


and atom_to_tll_atom (a:E.atom) : atom =
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
    E.Append (p1,p2,p3)    -> Append (path p1,path p2,path p3)
  | E.Reach (m,a1,a2,p)    -> Reach (mem m, addr a1, addr a2, path p)
  | E.OrderList(m,a1,a2)   -> OrderList (mem m, addr a1, addr a2)
  | E.In (a,s)             -> In (addr a, set s)
  | E.SubsetEq (s1,s2)     -> SubsetEq (set s1, set s2)
  | E.InTh (t,s)           -> InTh (tid t, setth s)
  | E.SubsetEqTh (s1,s2)   -> SubsetEqTh (setth s1, setth s2)
  | E.InElem (e,s)         -> InElem (elem_to_tll_elem e, setelem s)
  | E.SubsetEqElem (s1,s2) -> SubsetEqElem (setelem s1, setelem s2)
  | E.Less (i1,i2)         -> Less (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessEq (i1,i2)       -> LessEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.Greater (i1,i2)      -> Greater (int_to_tll_int i1, int_to_tll_int i2)
  | E.GreaterEq (i1,i2)    -> GreaterEq (int_to_tll_int i1, int_to_tll_int i2)
  | E.LessElem (e1,e2)     -> LessElem (elem e1, elem e2)
  | E.GreaterElem (e1,e2)  -> GreaterElem (elem e1, elem e2)
  | E.Eq (t1,t2)           -> Eq (term t1, term t2)
  | E.InEq (t1,t2)         -> InEq (term t1, term t2)
  | E.BoolVar v            -> BoolVar (variable_to_tll_var v)
  | E.PC (pc,t,pr)         -> PC (pc, shared_to_tll_shared t, pr)
  | E.PCUpdate (pc,t)      -> PCUpdate (pc, tid_to_tll_tid t)
  | E.PCRange (pc1,pc2,t,pr) -> PCRange (pc1, pc2, shared_to_tll_shared t, pr)
  | _                      -> raise(UnsupportedTllExpr(E.atom_to_str a))

and formula_to_tll_formula (phi:E.formula) : formula =
  Formula.formula_conv atom_to_tll_atom phi


(**********************  Generic Expression Functions  ********************)

let cast (phi:Expression.formula) : formula =
  formula_to_tll_formula phi

let cast_var (v:Expression.V.t) : V.t =
  variable_to_tll_var v

let tid_sort : sort = Tid

let tid_var (v:V.t) : tid = VarTh v

let no_tid : tid = NoTid

let to_str (phi:formula) : string = formula_to_str phi

let ineq_tid (t1:tid) (t2:tid) : formula =
  F.atom_to_formula (InEq(TidT t1, TidT t2))

let pc_form (i:int) (scope:V.shared_or_local) (pr:bool) : formula =
  F.atom_to_formula (PC(i,scope,pr))

let gen_fresh_tids (set:ThreadSet.t) (n:int) : ThreadSet.t =
  let gen_cand i = VarTh (build_var ("k_" ^ (string_of_int i))
                           Tid false V.Shared V.GlobalScope) in
  LeapLib.gen_fresh
    set ThreadSet.empty ThreadSet.add ThreadSet.mem gen_cand n

let param (p:V.shared_or_local) (phi:formula) =
  F.formula_trans param_fs (V.param_local_only p) phi
