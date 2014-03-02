open Printf
open LeapLib
open LeapVerbose

module F = Formula

type sort =
    Set
  | Elem
  | Tid
  | Addr
  | Cell
  | SetTh
  | SetElem
  | Path
  | Mem
  | Int
  | AddrArray
  | TidArray
  | Bool
  | Unknown

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = unit
  end )


type logic_op_t = AndOp | OrOp | ImpliesOp | IffOp | NotOp | NoneOp


type term =
    VarT              of V.t
  | SetT              of set
  | ElemT             of elem
  | TidT              of tid
  | AddrT             of addr
  | CellT             of cell
  | SetThT            of setth
  | SetElemT          of setelem
  | PathT             of path
  | MemT              of mem
  | IntT              of integer
  | AddrArrayT        of addrarr
  | TidArrayT         of tidarr
  | VarUpdate         of V.t * tid * term
and eq = term * term
and diseq = term * term
and set =
    VarSet            of V.t
  | EmptySet
  | Singl             of addr
  | Union             of set * set
  | Intr              of set * set
  | Setdiff           of set * set
  | PathToSet         of path
  | AddrToSet         of mem * addr * integer
and tid =
    VarTh             of V.t
  | NoTid
  | CellLockIdAt      of cell * integer
  | TidArrRd          of tidarr * integer
and elem =
    VarElem           of V.t
  | CellData          of cell
  | HavocSkiplistElem
  | LowestElem
  | HighestElem
and addr =
    VarAddr           of V.t
  | Null
  | ArrAt             of cell * integer
  | AddrArrRd         of addrarr * integer
and cell =
    VarCell           of V.t
  | Error
  | MkCell            of elem * addrarr * tidarr * integer
  | CellLockAt        of cell * integer * tid
  | CellUnlockAt      of cell * integer
  | CellAt            of mem * addr
and setth =
    VarSetTh          of V.t
  | EmptySetTh
  | SinglTh           of tid
  | UnionTh           of setth * setth
  | IntrTh            of setth * setth
  | SetdiffTh         of setth * setth
and setelem =
    VarSetElem        of V.t
  | EmptySetElem
  | SinglElem         of elem
  | UnionElem         of setelem * setelem
  | IntrElem          of setelem * setelem
  | SetToElems        of set * mem
  | SetdiffElem       of setelem * setelem
and path =
    VarPath           of V.t
  | Epsilon
  | SimplePath        of addr
  | GetPath           of mem * addr * addr * integer
and mem =
    VarMem            of V.t
  | Update            of mem * addr * cell
and integer =
    IntVal            of int
  | VarInt            of V.t
  | IntNeg            of integer
  | IntAdd            of integer * integer
  | IntSub            of integer * integer
  | IntMul            of integer * integer
  | IntDiv            of integer * integer
  | CellMax           of cell
  | HavocLevel
and addrarr =
  | VarAddrArray      of V.t
  | AddrArrayUp       of addrarr * integer * addr
  | CellArr           of cell
and tidarr =
  | VarTidArray       of V.t
  | TidArrayUp        of tidarr * integer * tid
  | CellTids          of cell
and atom =
    Append            of path * path * path
  | Reach             of mem * addr * addr * integer * path
  | OrderList         of mem * addr * addr
  | Skiplist          of mem * set * integer * addr * addr * setelem
  | In                of addr * set
  | SubsetEq          of set  * set
  | InTh              of tid * setth
  | SubsetEqTh        of setth * setth
  | InElem            of elem * setelem
  | SubsetEqElem      of setelem * setelem
  | Less              of integer * integer
  | Greater           of integer * integer
  | LessEq            of integer * integer
  | GreaterEq         of integer * integer
  | LessElem          of elem * elem
  | GreaterElem       of elem * elem
  | Eq                of eq
  | InEq              of diseq
  | BoolVar           of V.t
  | PC                of int * V.shared_or_local * bool
  | PCUpdate          of int * tid
  | PCRange           of int * int * V.shared_or_local * bool
and literal = atom F.literal
and conjunctive_formula = atom F.conjunctive_formula
and disjunctive_formula = atom F.disjunctive_formula
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
  | SkiplistProp

exception WrongType of term
exception No_variable_term of term
exception Incompatible_replacement of term * term
exception Not_tid_var of tid



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
  | CellLockIdAt _    -> false
  | TidArrRd _       -> false
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


module LiteralSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = literal
  end )


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
    mutable addrarr_f : ('info,'a) fold_ops_t -> 'info -> addrarr -> 'a;
    mutable tidarr_f : ('info,'a) fold_ops_t -> 'info -> tidarr -> 'a;
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
    addrarr_f : 'info -> addrarr -> 'a;
    tidarr_f : 'info -> tidarr -> 'a;
    atom_f : 'info -> atom -> 'a;
    term_f : 'info -> term -> 'a;
  }



let rec fold_addr (fs:('info,'a) fold_ops_t) (info:'info) (a:addr) : 'a =
  match a with
  | VarAddr v       -> fs.var_f fs info v
  | Null            -> fs.base info
  | ArrAt (c,i)     -> fs.concat (fs.cell_f fs info c) (fs.int_f fs info i)
  | AddrArrRd(aa,i) -> fs.concat (fs.addrarr_f fs info aa) (fs.int_f fs info i)

and fold_elem (fs:('info,'a) fold_ops_t) (info:'info) (e:elem) : 'a =
  match e with
  | VarElem v         -> fs.var_f fs info v
  | CellData c        -> fs.cell_f fs info c
  | HavocSkiplistElem -> fs.base info
  | LowestElem        -> fs.base info
  | HighestElem       -> fs.base info

and fold_tid (fs:('info,'a) fold_ops_t) (info:'info) (t:tid) : 'a =
  match t with
  | VarTh v            -> fs.var_f fs info v
  | NoTid              -> fs.base info
  | CellLockIdAt (c,i) -> fs.concat (fs.cell_f fs info c) (fs.int_f fs info i)
  | TidArrRd (tt,i)    -> fs.concat (fs.tidarr_f fs info tt) (fs.int_f fs info i)

and fold_int (fs:('info,'a) fold_ops_t) (info:'info) (i:integer) : 'a =
  match i with
  | IntVal _ -> fs.base info
  | VarInt v -> fs.var_f fs info v
  | IntNeg j -> fs.int_f fs info j
  | IntAdd (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntSub (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntMul (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | IntDiv (j1,j2) -> fs.concat (fs.int_f fs info j1) (fs.int_f fs info j2)
  | CellMax c -> fs.cell_f fs info c
  | HavocLevel -> fs.base info

and fold_cell (fs:('info,'a) fold_ops_t) (info:'info) (c:cell) : 'a =
  match c with
  | VarCell v          -> fs.var_f fs info v
  | Error              -> fs.base info
  | MkCell(e,aa,tt,i)  -> fs.concat (fs.elem_f fs info e)
                                    (fs.concat (fs.addrarr_f fs info aa)
                                               (fs.concat (fs.tidarr_f fs info tt)
                                                          (fs.int_f fs info i)))
  | CellLockAt(c,i,th) -> fs.concat (fs.cell_f fs info c)
                                    (fs.concat (fs.int_f fs info i)
                                               (fs.tid_f fs info th))
  | CellUnlockAt(c,i)  -> fs.concat (fs.cell_f fs info c) (fs.int_f fs info i)
  | CellAt(m,a)        -> fs.concat (fs.mem_f fs info m) (fs.addr_f fs info a)

and fold_mem (fs:('info,'a) fold_ops_t) (info:'info) (m:mem) : 'a =
  match m with
  | VarMem v      -> fs.var_f fs info v
  | Update(m,a,c) -> fs.concat (fs.mem_f fs info m)
                               (fs.concat (fs.addr_f fs info a)
                                          (fs.cell_f fs info c))

and fold_path (fs:('info,'a) fold_ops_t) (info:'info) (p:path) : 'a =
  match p with
  | VarPath v          -> fs.var_f fs info v
  | Epsilon            -> fs.base info
  | SimplePath(a)      -> fs.addr_f fs info a
  | GetPath(m,a1,a2,i) -> fs.concat (fs.mem_f fs info m)
                                    (fs.concat (fs.addr_f fs info a1)
                                               (fs.concat (fs.addr_f fs info a2)
                                                          (fs.int_f fs info i)))

and fold_set (fs:('info,'a) fold_ops_t) (info:'info) (s:set) : 'a =
  match s with
  | VarSet v         -> fs.var_f fs info v
  | EmptySet         -> fs.base info
  | Singl(a)         -> fs.addr_f fs info a
  | Union(s1,s2)     -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Intr(s1,s2)      -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | Setdiff(s1,s2)   -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | PathToSet(p)     -> fs.path_f fs info p
  | AddrToSet(m,a,i) -> fs.concat (fs.mem_f fs info m)
                                  (fs.concat (fs.addr_f fs info a)
                                             (fs.int_f fs info i))

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

and fold_addrarr (fs:('info,'a) fold_ops_t) (info:'info) (aa:addrarr) : 'a =
  match aa with
  | VarAddrArray v -> fs.var_f fs info v
  | AddrArrayUp (aa,i,a) -> fs.concat (fs.addrarr_f fs info aa)
                                      (fs.concat (fs.int_f fs info i)
                                                 (fs.addr_f fs info a))
  | CellArr c -> fs.cell_f fs info c

and fold_tidarr (fs:('info,'a) fold_ops_t) (info:'info) (tt:tidarr) : 'a =
  match tt with
  | VarTidArray v -> fs.var_f fs info v
  | TidArrayUp (tt,i,th) -> fs.concat (fs.tidarr_f fs info tt)
                                      (fs.concat (fs.int_f fs info i)
                                                 (fs.tid_f fs info th))
  | CellTids c -> fs.cell_f fs info c

and fold_atom (fs:('info,'a) fold_ops_t) (info:'info) (a:atom) : 'a =
  match a with
  | Append(p1,p2,p3)          -> fs.concat (fs.path_f fs info p1)
                                    (fs.concat (fs.path_f fs info p2)
                                      (fs.path_f fs info p3))
  | Reach(m,a1,a2,i,p)        -> fs.concat (fs.mem_f fs info m)
                                    (fs.concat (fs.addr_f fs info a1)
                                        (fs.concat (fs.addr_f fs info a2)
                                            (fs.concat (fs.int_f fs info i)
                                                (fs.path_f fs info p))))
  | OrderList(m,a1,a2)        -> fs.concat (fs.mem_f fs info m)
                                    (fs.concat (fs.addr_f fs info a1)
                                        (fs.addr_f fs info a2))
  | Skiplist (m,s,i,a1,a2,se) -> fs.concat (fs.mem_f fs info m)
                                    (fs.concat (fs.set_f fs info s)
                                        (fs.concat (fs.int_f fs info i)
                                            (fs.concat (fs.addr_f fs info a1)
                                                (fs.concat (fs.addr_f fs info a2)
                                                    (fs.setelem_f fs info se)))))
  | In(a,s)                   -> fs.concat (fs.addr_f fs info a) (fs.set_f fs info s)
  | SubsetEq(s1,s2)           -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
  | InTh(th,st)               -> fs.concat (fs.tid_f fs info th) (fs.setth_f fs info st)
  | SubsetEqTh(st1,st2)       -> fs.concat (fs.setth_f fs info st1)
                                           (fs.setth_f fs info st2)
  | InElem(e,se)              -> fs.concat (fs.elem_f fs info e)
                                           (fs.setelem_f fs info se)
  | SubsetEqElem(se1,se2)     -> fs.concat (fs.setelem_f fs info se1)
                                           (fs.setelem_f fs info se2)
  | Less(i1,i2)               -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessEq(i1,i2)             -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | Greater(i1,i2)            -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | GreaterEq(i1,i2)          -> fs.concat (fs.int_f fs info i1)
                                           (fs.int_f fs info i2)
  | LessElem(e1,e2)           -> fs.concat (fs.elem_f fs info e1)
                                           (fs.elem_f fs info e2)
  | GreaterElem(e1,e2)        -> fs.concat (fs.elem_f fs info e1)
                                           (fs.elem_f fs info e2)
  | Eq((x,y))                 -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | InEq((x,y))               -> fs.concat (fs.term_f fs info x)
                                           (fs.term_f fs info y)
  | BoolVar v                 -> fs.var_f fs info v
  | PC(pc,th,pr)              -> (match th with
                                   | V.Shared -> fs.base info
                                   | V.Local t -> fs.var_f fs info t)
  | PCUpdate (pc,th)          -> fs.tid_f fs info th
  | PCRange(pc1,pc2,th,pr)    -> (match th with
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
  | AddrArrayT aa     -> fs.addrarr_f fs info aa
  | TidArrayT tt      -> fs.tidarr_f fs info tt
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
              ?(addrarr_f=fold_addrarr)
              ?(tidarr_f=fold_tidarr)
              ?(atom_f=fold_atom)
              ?(term_f=fold_term)
              (base:('info -> 'a))
              (concat:('a -> 'a -> 'a))
              (var_f :(('info,'a) fold_ops_t -> 'info -> V.t -> 'a))
    : ('info,'a) folding_t =
  let fs = {
    addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
    int_f = int_f; cell_f = cell_f; mem_f = mem_f;
    path_f = path_f; set_f = set_f; setelem_f = setelem_f;
    setth_f = setth_f; addrarr_f = addrarr_f; tidarr_f = tidarr_f;
    atom_f = atom_f; term_f = term_f;
    base = base; concat = concat; var_f = var_f; } in
  { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
    int_f = int_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
    path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
    setth_f = setth_f fs; addrarr_f = addrarr_f fs; tidarr_f = tidarr_f fs;
    atom_f = atom_f fs; term_f = term_f fs;
    var_f = var_f fs; }


(**********  Mapping  ***************)

type 'info map_ops_t =
  {
    var_f : 'info map_ops_t -> 'info -> V.t -> V.t;
    mutable addr_f : 'info map_ops_t -> 'info -> addr -> addr;
    mutable elem_f : 'info map_ops_t -> 'info -> elem -> elem;
    mutable tid_f : 'info map_ops_t -> 'info -> tid -> tid;
    mutable int_f : 'info map_ops_t -> 'info -> integer -> integer;
    mutable cell_f : 'info map_ops_t -> 'info -> cell -> cell;
    mutable mem_f : 'info map_ops_t -> 'info -> mem -> mem;
    mutable path_f : 'info map_ops_t -> 'info -> path -> path;
    mutable set_f : 'info map_ops_t -> 'info -> set -> set;
    mutable setelem_f : 'info map_ops_t -> 'info -> setelem -> setelem;
    mutable setth_f : 'info map_ops_t -> 'info -> setth -> setth;
    mutable addrarr_f : 'info map_ops_t -> 'info -> addrarr -> addrarr;
    mutable tidarr_f : 'info map_ops_t -> 'info -> tidarr -> tidarr;
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
    addrarr_f : 'info -> addrarr -> addrarr;
    tidarr_f : 'info -> tidarr -> tidarr;
    atom_f : 'info -> atom -> atom;
    term_f : 'info -> term -> term;
  }



let rec map_addr (fs:'info map_ops_t) (info:'info) (a:addr) : addr =
  match a with
  | VarAddr v       -> VarAddr (fs.var_f fs info v)
  | Null            -> Null
  | ArrAt (c,i)     -> ArrAt (fs.cell_f fs info c, fs.int_f fs info i)
  | AddrArrRd(aa,i) -> AddrArrRd (fs.addrarr_f fs info aa, fs.int_f fs info i)

and map_elem (fs:'info map_ops_t) (info:'info) (e:elem) : elem =
  match e with
  | VarElem v         -> VarElem (fs.var_f fs info v)
  | CellData c        -> CellData (fs.cell_f fs info c)
  | HavocSkiplistElem -> HavocSkiplistElem
  | LowestElem        -> LowestElem
  | HighestElem       -> HighestElem

and map_tid (fs:'info map_ops_t) (info:'info) (t:tid) : tid =
  match t with
  | VarTh v            -> VarTh (fs.var_f fs info v)
  | NoTid              -> NoTid
  | CellLockIdAt (c,i) -> CellLockIdAt (fs.cell_f fs info c, fs.int_f fs info i)
  | TidArrRd (tt,i)    -> TidArrRd (fs.tidarr_f fs info tt, fs.int_f fs info i)

and map_int (fs:'info map_ops_t) (info:'info) (i:integer) : integer =
  match i with
  | IntVal j -> IntVal j
  | VarInt v -> VarInt (fs.var_f fs info v)
  | IntNeg j -> IntNeg (fs.int_f fs info j)
  | IntAdd (j1,j2) -> IntAdd (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntSub (j1,j2) -> IntSub (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntMul (j1,j2) -> IntMul (fs.int_f fs info j1, fs.int_f fs info j2)
  | IntDiv (j1,j2) -> IntDiv (fs.int_f fs info j1, fs.int_f fs info j2)
  | CellMax c -> CellMax (fs.cell_f fs info c)
  | HavocLevel -> HavocLevel

and map_cell (fs:'info map_ops_t) (info:'info) (c:cell) : cell =
  match c with
  | VarCell v          -> VarCell (fs.var_f fs info v)
  | Error              -> Error
  | MkCell(e,aa,tt,i)  -> MkCell (fs.elem_f fs info e,
                                  fs.addrarr_f fs info aa,
                                  fs.tidarr_f fs info tt,
                                  fs.int_f fs info i)
  | CellLockAt(c,i,th) -> CellLockAt(fs.cell_f fs info c,
                                     fs.int_f fs info i,
                                     fs.tid_f fs info th)
  | CellUnlockAt(c,i)  -> CellUnlockAt (fs.cell_f fs info c, fs.int_f fs info i)
  | CellAt(m,a)        -> CellAt (fs.mem_f fs info m, fs.addr_f fs info a)

and map_mem (fs:'info map_ops_t) (info:'info) (m:mem) : mem =
  match m with
  | VarMem v      -> VarMem (fs.var_f fs info v)
  | Update(m,a,c) -> Update (fs.mem_f fs info m,
                             fs.addr_f fs info a,
                             fs.cell_f fs info c)

and map_path (fs:'info map_ops_t) (info:'info) (p:path) : path =
  match p with
  | VarPath v          -> VarPath (fs.var_f fs info v)
  | Epsilon            -> Epsilon
  | SimplePath(a)      -> SimplePath (fs.addr_f fs info a)
  | GetPath(m,a1,a2,i) -> GetPath (fs.mem_f fs info m,
                                   fs.addr_f fs info a1,
                                   fs.addr_f fs info a2,
                                   fs.int_f fs info i)

and map_set (fs:'info map_ops_t) (info:'info) (s:set) : set =
  match s with
  | VarSet v         -> VarSet (fs.var_f fs info v)
  | EmptySet         -> EmptySet
  | Singl(a)         -> Singl (fs.addr_f fs info a)
  | Union(s1,s2)     -> Union (fs.set_f fs info s1, fs.set_f fs info s2)
  | Intr(s1,s2)      -> Intr (fs.set_f fs info s1, fs.set_f fs info s2)
  | Setdiff(s1,s2)   -> Setdiff (fs.set_f fs info s1, fs.set_f fs info s2)
  | PathToSet(p)     -> PathToSet (fs.path_f fs info p)
  | AddrToSet(m,a,i) -> AddrToSet (fs.mem_f fs info m,
                                   fs.addr_f fs info a,
                                   fs.int_f fs info i)

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
  | UnionTh(st1,st2)   -> UnionTh (fs.setth_f fs info st1, fs.setth_f fs info st2)
  | IntrTh(st1,st2)    -> IntrTh (fs.setth_f fs info st1, fs.setth_f fs info st2)
  | SetdiffTh(st1,st2) -> SetdiffTh (fs.setth_f fs info st1, fs.setth_f fs info st2)

and map_addrarr (fs:'info map_ops_t) (info:'info) (aa:addrarr) : addrarr =
  match aa with
  | VarAddrArray v -> VarAddrArray (fs.var_f fs info v)
  | AddrArrayUp (aa,i,a) -> AddrArrayUp (fs.addrarr_f fs info aa,
                                         fs.int_f fs info i,
                                         fs.addr_f fs info a)
  | CellArr c -> CellArr (fs.cell_f fs info c)

and map_tidarr (fs:'info map_ops_t) (info:'info) (tt:tidarr) : tidarr =
  match tt with
  | VarTidArray v -> VarTidArray (fs.var_f fs info v)
  | TidArrayUp (tt,i,th) -> TidArrayUp (fs.tidarr_f fs info tt,
                                        fs.int_f fs info i,
                                        fs.tid_f fs info th)
  | CellTids c -> CellTids (fs.cell_f fs info c)

and map_atom (fs:'info map_ops_t) (info:'info) (a:atom) : atom =
  match a with
  | Append(p1,p2,p3)          -> Append (fs.path_f fs info p1,
                                         fs.path_f fs info p2,
                                         fs.path_f fs info p3)
  | Reach(m,a1,a2,i,p)        -> Reach (fs.mem_f fs info m,
                                        fs.addr_f fs info a1,
                                        fs.addr_f fs info a2,
                                        fs.int_f fs info i,
                                        fs.path_f fs info p)
  | OrderList(m,a1,a2)        -> OrderList (fs.mem_f fs info m,
                                            fs.addr_f fs info a1,
                                            fs.addr_f fs info a2)
  | Skiplist (m,s,i,a1,a2,se) -> Skiplist (fs.mem_f fs info m,
                                           fs.set_f fs info s,
                                           fs.int_f fs info i,
                                           fs.addr_f fs info a1,
                                           fs.addr_f fs info a2,
                                           fs.setelem_f fs info se)
  | In(a,s)                   -> In (fs.addr_f fs info a, fs.set_f fs info s)
  | SubsetEq(s1,s2)           -> SubsetEq (fs.set_f fs info s1, fs.set_f fs info s2)
  | InTh(th,st)               -> InTh (fs.tid_f fs info th, fs.setth_f fs info st)
  | SubsetEqTh(st1,st2)       -> SubsetEqTh (fs.setth_f fs info st1,
                                             fs.setth_f fs info st2)
  | InElem(e,se)              -> InElem (fs.elem_f fs info e,
                                         fs.setelem_f fs info se)
  | SubsetEqElem(se1,se2)     -> SubsetEqElem (fs.setelem_f fs info se1,
                                               fs.setelem_f fs info se2)
  | Less(i1,i2)               -> Less (fs.int_f fs info i1,
                                       fs.int_f fs info i2)
  | LessEq(i1,i2)             -> LessEq (fs.int_f fs info i1,
                                         fs.int_f fs info i2)
  | Greater(i1,i2)            -> Greater (fs.int_f fs info i1,
                                          fs.int_f fs info i2)
  | GreaterEq(i1,i2)          -> GreaterEq (fs.int_f fs info i1,
                                            fs.int_f fs info i2)
  | LessElem(e1,e2)           -> LessElem (fs.elem_f fs info e1,
                                           fs.elem_f fs info e2)
  | GreaterElem(e1,e2)        -> GreaterElem (fs.elem_f fs info e1,
                                              fs.elem_f fs info e2)
  | Eq((x,y))                 -> Eq (fs.term_f fs info x,
                                     fs.term_f fs info y)
  | InEq((x,y))               -> InEq (fs.term_f fs info x,
                                       fs.term_f fs info y)
  | BoolVar v                 -> BoolVar (fs.var_f fs info v)
  | PC(pc,th,pr)              -> PC(pc, (match th with
                                         | V.Shared -> V.Shared
                                         | V.Local t -> V.Local(fs.var_f fs info t)),
                                    pr)
  | PCUpdate (pc,th)          -> PCUpdate (pc, fs.tid_f fs info th)
  | PCRange(pc1,pc2,th,pr)    -> PCRange (pc1, pc2,
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
  | AddrArrayT aa     -> AddrArrayT (fs.addrarr_f fs info aa)
  | TidArrayT tt      -> TidArrayT (fs.tidarr_f fs info tt)
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
             ?(addrarr_f=map_addrarr)
             ?(tidarr_f=map_tidarr)
             ?(atom_f=map_atom)
             ?(term_f=map_term)
             (var_f :('info map_ops_t -> 'info -> V.t -> V.t))
    : 'info mapping_t =
  let fs : 'info map_ops_t = {
    addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
    int_f = int_f; cell_f = cell_f; mem_f = mem_f;
    path_f = path_f; set_f = set_f; setelem_f = setelem_f;
    setth_f = setth_f; addrarr_f = addrarr_f; tidarr_f = tidarr_f;
    atom_f = atom_f; term_f = term_f; var_f = var_f; } in
  { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
    int_f = int_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
    path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
    setth_f = setth_f fs; addrarr_f = addrarr_f fs; tidarr_f = tidarr_f fs;
    atom_f = atom_f fs; term_f = term_f fs; var_f = var_f fs; }



(************************************************)
(*  Obtain the set of variables from a formula  *)
(************************************************)


let get_varset_from_param (v:V.t) : V.VarSet.t =
  match V.parameter v with
  | V.Local t -> V.VarSet.singleton t
  | V.Shared -> V.VarSet.empty

let varset_fold =
  make_fold (fun _ -> V.VarSet.empty) V.VarSet.union
            (fun _ _ v -> V.VarSet.union (V.VarSet.singleton v)
                                         (get_varset_from_param v))
  ~atom_f:(fun fs instances a ->
      match a with
      | Eq (x,y) -> if instances then begin
                      match (x,y) with
                      | (VarUpdate _, _) -> fs.term_f fs instances x
                      | (_, VarUpdate _) -> fs.term_f fs instances y
                      | _ -> fs.concat (fs.term_f fs instances x)
                                       (fs.term_f fs instances y)
                    end else begin
                      fs.concat (fs.term_f fs instances x)
                                (fs.term_f fs instances y)
                    end
      | _ -> fold_atom fs instances a)
  ~term_f:(fun fs instances t ->
      match t with
      | VarUpdate (v,pc,t) -> if instances then
                                fs.term_f fs instances t
                              else
                                fs.concat (V.VarSet.singleton v)
                                    (fs.concat (fs.term_f fs instances t)
                                        (get_varset_from_param v))
      | _ -> fold_term fs instances t)


let varset_fs = F.make_fold
                  F.GenericLiteralFold
                  (varset_fold.atom_f)
                  (fun info -> V.VarSet.empty)
                  (V.VarSet.union)


let get_varset_from_conj (instances:bool) (cf:conjunctive_formula) : V.VarSet.t =
  F.conjunctive_formula_fold varset_fs instances cf

let get_varset_from_formula (instances:bool) (phi:formula) : V.VarSet.t =
  F.formula_fold varset_fs instances phi



let varset (phi:formula) : V.VarSet.t =
  get_varset_from_formula false phi


let varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
  get_varset_from_conj false cf


let varset (phi:formula) : V.VarSet.t =
  get_varset_from_formula false phi


let varset_instances_from_conj (cf:conjunctive_formula) : V.VarSet.t =
  get_varset_from_conj true cf


let varset_instances (phi:formula) : V.VarSet.t =
  get_varset_from_formula true phi


let varset_of_sort_from_literal (lit:literal) (s:sort) =
  V.varset_of_sort (varset (F.Literal lit)) s


let varset_of_sort_from_conj (phi:conjunctive_formula) (s:sort) =
  V.varset_of_sort (varset_from_conj phi) s


let varset_of_sort (phi:formula) (s:sort) =
  V.varset_of_sort (varset phi) s


let varset_instances_of_sort_from_conj (phi:conjunctive_formula) (s:sort) =
  V.varset_of_sort (varset_instances_from_conj phi) s


let varset_instances_of_sort (phi:formula) (s:sort) =
  V.varset_of_sort (varset_instances phi) s


let varlist_from_conj (phi:conjunctive_formula) : V.t list =
  V.VarSet.elements (varset_from_conj phi)


let varlist (phi:formula) : V.t list =
  V.VarSet.elements (varset phi)


let varidlist_of_sort_from_conj (phi:conjunctive_formula) (s:sort) : V.id list =
  V.varidlist_of_sort (varlist_from_conj phi) s


let varidlist_of_sort (phi:formula) (s:sort) : V.id list =
  V.varidlist_of_sort (varlist phi) s


let rec get_termset_atom (a:atom) : TermSet.t =
  let add_list = List.fold_left (fun s e -> TermSet.add e s) TermSet.empty in
  match a with
  | Append(p1,p2,p3)         -> add_list [PathT p1; PathT p2; PathT p3]
  | Reach(m,a1,a2,l,p)       -> add_list [MemT m;AddrT a1;AddrT a2;IntT l;PathT p]
  | OrderList(m,a1,a2)       -> add_list [MemT m; AddrT a1; AddrT a2]
  | Skiplist(m,s,l,a1,a2,es) -> add_list [MemT m; SetT s; IntT l; AddrT a1; AddrT a2; SetElemT es]
  | In(a,s)                  -> add_list [AddrT a; SetT s]
  | SubsetEq(s1,s2)          -> add_list [SetT s1; SetT s2]
  | InTh(th,st)              -> add_list [TidT th; SetThT st]
  | SubsetEqTh(st1,st2)      -> add_list [SetThT st1; SetThT st2]
  | InElem(e,se)             -> add_list [ElemT e; SetElemT se]
  | SubsetEqElem(se1,se2)    -> add_list [SetElemT se1; SetElemT se2]
  | Less (i,j)               -> add_list [IntT i; IntT j]
  | Greater (i,j)            -> add_list [IntT i; IntT j]
  | LessEq (i,j)             -> add_list [IntT i; IntT j]
  | GreaterEq (i,j)          -> add_list [IntT i; IntT j]
  | LessElem(e1,e2)          -> add_list [ElemT e1; ElemT e2]
  | GreaterElem(e1,e2)       -> add_list [ElemT e1; ElemT e2]
  | Eq((x,y))                -> add_list [x;y]
  | InEq((x,y))              -> add_list [x;y]
  | BoolVar v                -> add_list [VarT v]
  | PC(pc,th,pr)             -> (match th with
                                 | V.Shared  -> TermSet.empty
                                 | V.Local t -> add_list [TidT (VarTh t)])
  | PCUpdate (pc,th)         -> add_list [TidT th]
  | PCRange(pc1,pc2,th,pr)   -> (match th with
                                 | V.Shared  -> TermSet.empty
                                 | V.Local t -> add_list [TidT (VarTh t)])

let termset_fs = F.make_fold
                   F.GenericLiteralFold
                   (fun info a -> get_termset_atom a)
                   (fun info -> TermSet.empty)
                   (TermSet.union)

let get_termset_from_conjformula (cf:conjunctive_formula) : TermSet.t =
  F.conjunctive_formula_fold termset_fs () cf

let get_termset_from_formula (phi:formula) : TermSet.t =
  F.formula_fold termset_fs () phi



let termset (phi:formula) : TermSet.t =
  get_termset_from_formula phi


let termset_from_conj (cf:conjunctive_formula) : TermSet.t =
  get_termset_from_conjformula cf


let filter_termset_with_sort (all:TermSet.t) (s:sort) : TermSet.t =
  let match_sort (t:term) : bool =
    match s with
    | Set       -> (match t with | SetT _       -> true | _ -> false)
    | Elem      -> (match t with | ElemT _      -> true | _ -> false)
    | Tid      -> (match t with | TidT _      -> true | _ -> false)
    | Addr      -> (match t with | AddrT _      -> true | _ -> false)
    | Cell      -> (match t with | CellT _      -> true | _ -> false)
    | SetTh     -> (match t with | SetThT _     -> true | _ -> false)
    | SetElem   -> (match t with | SetElemT _   -> true | _ -> false)
    | Path      -> (match t with | PathT _      -> true | _ -> false)
    | Mem       -> (match t with | MemT _       -> true | _ -> false)
    | Int       -> (match t with | IntT _       -> true | _ -> false)
    | AddrArray -> (match t with | AddrArrayT _ -> true | _ -> false)
    | TidArray  -> (match t with | TidArrayT _  -> true | _ -> false)
    | Bool      -> (match t with | VarT v       -> (V.sort v = Bool)
                                 | _            -> false)
    | Unknown -> false in
  TermSet.fold (fun t set ->
    if match_sort t then
      TermSet.add t set
    else
      set
  ) all TermSet.empty



(* is_variable *)
let is_var_fold =
  make_fold (fun _ -> false) (fun _ _ -> false) (fun _ _ _ -> true)


(* TODO: propagate equalities of vars x = y *)


let is_flat_fold =
  make_fold (fun _ -> true) (&&) (fun _ _ _ -> true)
  ~atom_f:(fun fs info a -> match a with
                            | BoolVar _
                            | PC _
                            | PCUpdate _
                            | PCRange _ -> true
                            | _ -> fold_atom fs info a)

(*******************)
(* PRETTY PRINTERS *)
(* WIHOUT FOLD     *)
(*******************)


let rec atom_to_str a =
  match a with
  | Append(p1,p2,pres)                 -> Printf.sprintf "append(%s,%s,%s)"
                                            (path_to_str p1) (path_to_str p2)
                                            (path_to_str pres)
  | Reach(h,a_from,a_to,l,p)           -> Printf.sprintf "reach(%s,%s,%s,%s,%s)"
                                            (mem_to_str h) (addr_to_str a_from)
                                            (addr_to_str a_to) (int_to_str l)
                                            (path_to_str p)
  | OrderList(h,a_from,a_to)           -> Printf.sprintf "orderlist(%s,%s,%s)"
                                            (mem_to_str h) (addr_to_str a_from)
                                            (addr_to_str a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Printf.sprintf "skiplist(%s,%s,%s,%s,%s,%s)"
                                            (mem_to_str h)
                                            (set_to_str s)
                                            (int_to_str l)
                                            (addr_to_str a_from)
                                            (addr_to_str a_to)
                                            (setelem_to_str elems)
  | In(a,s)                            -> Printf.sprintf "%s in %s "
                                            (addr_to_str a) (set_to_str s)
  | SubsetEq(s_in,s_out)               -> Printf.sprintf "%s subseteq %s"
                                            (set_to_str s_in) (set_to_str s_out)
  | InTh(th,s)                         -> Printf.sprintf "%s inTh %s"
                                            (tid_to_str th) (setth_to_str s)
  | SubsetEqTh(s_in,s_out)             -> Printf.sprintf "%s subseteqTh %s"
                                            (setth_to_str s_in) (setth_to_str s_out)
  | InElem(e,s)                        -> Printf.sprintf "%s inElem %s"
                                            (elem_to_str e) (setelem_to_str s)
  | SubsetEqElem(s_in,s_out)           -> Printf.sprintf "%s subseteqElem %s"
                                            (setelem_to_str s_in) (setelem_to_str s_out)
  | Less (i1,i2)                       -> Printf.sprintf "%s < %s"
                                            (int_to_str i1) (int_to_str i2)
  | Greater (i1,i2)                    -> Printf.sprintf "%s > %s"
                                            (int_to_str i1) (int_to_str i2)
  | LessEq (i1,i2)                     -> Printf.sprintf "%s <= %s"
                                            (int_to_str i1) (int_to_str i2)
  | GreaterEq (i1,i2)                  -> Printf.sprintf "%s >= %s"
                                            (int_to_str i1) (int_to_str i2)
  | LessElem(e1,e2)                    -> Printf.sprintf "%s < %s"
                                            (elem_to_str e1) (elem_to_str e2)
  | GreaterElem(e1,e2)                 -> Printf.sprintf "%s < %s"
                                            (elem_to_str e1) (elem_to_str e2)
  | Eq(exp)                            -> eq_to_str (exp)
  | InEq(exp)                          -> diseq_to_str (exp)
  | BoolVar v                          -> V.to_str v
  | PC (pc,t,pr)                       -> let pc_str = if pr then "pc'" else "pc" in
                                          let th_str = V.shared_or_local_to_str t in
                                          Printf.sprintf "%s(%s) = %i" pc_str th_str pc
  | PCUpdate (pc,t)                    -> let th_str = tid_to_str t in
                                          Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,t,pr)             -> let pc_str = if pr then "pc'" else "pc" in
                                          let th_str = V.shared_or_local_to_str t in
                                          Printf.sprintf "%i <= %s(%s) <= %i"
                                                          pc1 pc_str th_str pc2
and mem_to_str expr =
  match expr with
      VarMem(v) -> V.to_str v
    | Update(mem,add,cell) -> Printf.sprintf "upd(%s,%s,%s)"
        (mem_to_str mem) (addr_to_str add) (cell_to_str cell)
and int_to_str expr =
  match expr with
      IntVal i       -> string_of_int i
    | VarInt v       -> V.to_str v
    | IntNeg i       -> Printf.sprintf "-%s" (int_to_str i)
    | IntAdd (i1,i2) -> Printf.sprintf "%s + %s" (int_to_str i1) (int_to_str i2)
    | IntSub (i1,i2) -> Printf.sprintf "%s - %s" (int_to_str i1) (int_to_str i2)
    | IntMul (i1,i2) -> Printf.sprintf "%s * %s" (int_to_str i1) (int_to_str i2)
    | IntDiv (i1,i2) -> Printf.sprintf "%s / %s" (int_to_str i1) (int_to_str i2)
    | CellMax c      -> Printf.sprintf "%s.max" (cell_to_str c)
    | HavocLevel     -> Printf.sprintf "havocLevel()"
and addrarr_to_str expr =
  match expr with
      VarAddrArray v       -> V.to_str v
    | AddrArrayUp (aa,i,a) -> Printf.sprintf "%s {%s <- %s}"
                                (addrarr_to_str aa) (int_to_str i) (addr_to_str a)
    | CellArr c            -> Printf.sprintf "%s.arr" (cell_to_str c)
and tidarr_to_str expr =
  match expr with
      VarTidArray v       -> V.to_str v
    | TidArrayUp (tt,i,t) -> Printf.sprintf "%s {%s <- %s}"
                               (tidarr_to_str tt) (int_to_str i) (tid_to_str t)
    | CellTids c          -> Printf.sprintf "%s.tids" (cell_to_str c)
and path_to_str expr =
  match expr with
      VarPath(v)                 -> V.to_str v
    | Epsilon                    -> Printf.sprintf "epsilon"
    | SimplePath(addr)           -> Printf.sprintf "[ %s ]" (addr_to_str addr)
    | GetPath(mem,a_from,a_to,l) -> Printf.sprintf "getp(%s,%s,%s,%s)"
                                      (mem_to_str mem)
                                      (addr_to_str a_from)
                                      (addr_to_str a_to)
                                      (int_to_str l)
and set_to_str e =
  match e with
      VarSet(v)           -> V.to_str v
    | EmptySet            -> "EmptySet"
    | Singl(addr)         -> Printf.sprintf "{ %s }" (addr_to_str addr)
    | Union(s1,s2)        -> Printf.sprintf "%s Union %s"
                              (set_to_str s1) (set_to_str s2)
    | Intr(s1,s2)         -> Printf.sprintf "%s Intr %s"
                              (set_to_str s1) (set_to_str s2)
    | Setdiff(s1,s2)      -> Printf.sprintf "%s SetDiff %s"
                              (set_to_str s1) (set_to_str s2)
    | PathToSet(path)     -> Printf.sprintf "path2set(%s)"
                              (path_to_str path)
    | AddrToSet(mem,a,l)  -> Printf.sprintf "addr2set(%s,%s,%s)"
                              (mem_to_str mem) (addr_to_str a)
                              (int_to_str l)
and setth_to_str e =
  match e with
      VarSetTh(v)  -> V.to_str v
    | EmptySetTh  -> "EmptySetTh"
    | SinglTh(th) -> Printf.sprintf "[ %s ]" (tid_to_str th)
    | UnionTh(s_1,s_2) -> Printf.sprintf "%s UnionTh %s"
                            (setth_to_str s_1) (setth_to_str s_2)
    | IntrTh(s_1,s_2) -> Printf.sprintf "%s IntrTh %s"
                            (setth_to_str s_1) (setth_to_str s_2)
    | SetdiffTh(s_1,s_2) -> Printf.sprintf "%s SetDiffTh %s"
                            (setth_to_str s_1) (setth_to_str s_2)
and setelem_to_str e =
  match e with
      VarSetElem(v)  -> V.to_str v
    | EmptySetElem  -> "EmptySetElem"
    | SinglElem(e) -> Printf.sprintf "[ %s ]" (elem_to_str e)
    | UnionElem(s_1,s_2) -> Printf.sprintf "%s UnionElem %s"
                            (setelem_to_str s_1) (setelem_to_str s_2)
    | IntrElem(s_1,s_2) -> Printf.sprintf "%s IntrElem %s"
                            (setelem_to_str s_1) (setelem_to_str s_2)
    | SetToElems(s,m) -> Printf.sprintf "SetToElems(%s,%s)"
                            (set_to_str s) (mem_to_str m)
    | SetdiffElem(s_1,s_2) -> Printf.sprintf "%s SetDiffElem %s"
                            (setelem_to_str s_1) (setelem_to_str s_2)
and cell_to_str e =
  match e with
      VarCell(v)            -> V.to_str v
    | Error                 -> "Error"
    | MkCell(data,aa,tt,l)  -> Printf.sprintf "mkcell(%s,%s,%s,%s)"
                                 (elem_to_str data) (addrarr_to_str aa)
                                 (tidarr_to_str tt) (int_to_str l)
    | CellLockAt(cell,l,th) -> Printf.sprintf "%s.lock(%s,%s)"
                                 (cell_to_str cell) (int_to_str l) (tid_to_str th)
    | CellUnlockAt(cell,l)  -> Printf.sprintf "%s.unlock(%s)"
                                 (cell_to_str cell) (int_to_str l)
    | CellAt(mem,addr)      -> Printf.sprintf "%s [ %s ]"
                                 (mem_to_str mem) (addr_to_str addr)
and addr_to_str expr =
  match expr with
      VarAddr(v)            -> V.to_str v
    | Null                  -> "null"
    | ArrAt(cell,l)        -> Printf.sprintf "%s.next(%s)"
                                 (cell_to_str cell) (int_to_str l)
    | AddrArrRd (aa,i)      -> Printf.sprintf "%s[%s]"
                                 (addrarr_to_str aa) (int_to_str i)
and tid_to_str th =
  match th with
      VarTh(v)             -> V.to_str v
    | NoTid               -> Printf.sprintf "NoTid"
    | CellLockIdAt(cell,l) -> Printf.sprintf "%s.lockid(%s)"
                                (cell_to_str cell) (int_to_str l)
    | TidArrRd (tt,i)     -> Printf.sprintf "%s[%s]"
                                (tidarr_to_str tt) (int_to_str i)
and eq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s = %s" (term_to_str e1) (term_to_str e2)
and diseq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s != %s" (term_to_str e1) (term_to_str e2)
and elem_to_str elem =
  match elem with
      VarElem(v)         -> V.to_str v
    | CellData(cell)     -> Printf.sprintf "%s.data" (cell_to_str cell)
    | HavocSkiplistElem  -> "havocSkiplistElem()"
    | LowestElem         -> "lowestElem"
    | HighestElem        -> "highestElem"
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
    | IntT(i)            -> (int_to_str i)
    | AddrArrayT(aa)     -> (addrarr_to_str aa)
    | TidArrayT(tt)      -> (tidarr_to_str tt)
    | VarUpdate (v,th,t) -> let v_str = V.to_str v in
                            let th_str = tid_to_str th in
                            let t_str = term_to_str t in
                              Printf.sprintf "%s{%s<-%s}" v_str th_str t_str

let literal_to_str (l:literal) : string =
  F.literal_to_str atom_to_str l

let conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  F.conjunctive_formula_to_str atom_to_str cf

let disjunctive_formula_to_str (df:disjunctive_formula) : string =
  F.disjunctive_formula_to_str atom_to_str df

let formula_to_str (phi:formula) : string =
  F.formula_to_str atom_to_str phi



let sort_to_str s =
  match s with
    | Set       -> "Set"
    | Elem      -> "Elem"
    | Tid       -> "Tid"
    | Addr      -> "Addr"
    | Cell      -> "Cell"
    | SetTh     -> "SetTh"
    | SetElem   -> "SetElem"
    | Path      -> "Path"
    | Mem       -> "Mem"
    | Int       -> "Int"
    | AddrArray -> "AddrArray"
    | TidArray  -> "TidArray"
    | Bool      -> "Bool"
    | Unknown   -> "Unknown"


let print_atom a =
  Printer.generic atom_to_str a

let print_formula f =
  Printer.generic formula_to_str f 

let print_conjunctive_formula f = 
  Printer.generic conjunctive_formula_to_str f

let print_literal b =
  Printer.generic literal_to_str b

let print_addr a =
  Printer.generic addr_to_str a

let print_cell  c =
  Printer.generic cell_to_str c

let print_elem  e =
  Printer.generic elem_to_str e

let print_tid  t =
  Printer.generic tid_to_str t

let print_mem   m =
  Printer.generic mem_to_str m

let print_path  p =
  Printer.generic path_to_str p

let print_set   s =
  Printer.generic set_to_str s

let print_setth sth =
  Printer.generic setth_to_str sth




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



let voc_fs = F.make_fold
               F.GenericLiteralFold
               (voc_fold.atom_f)
               (fun info -> ThreadSet.empty)
               (ThreadSet.union)

let voc_literal (l:literal) : ThreadSet.t =
  F.literal_fold voc_fs () l

let voc_conjunctive_formula (cf:conjunctive_formula) : ThreadSet.t =
  F.conjunctive_formula_fold voc_fs () cf

let voc_formula (phi:formula) : ThreadSet.t =
  F.formula_fold voc_fs () phi



let voc (phi:formula) : ThreadSet.t =
  voc_formula phi


let unprimed_voc (phi:formula) : ThreadSet.t =
  ThreadSet.filter (is_primed_tid>>not) (voc phi)





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
        match i with
        | HavocLevel -> SortSet.empty
        | _ -> SortSet.add Int (fold_int fs info i))
    ~addrarr_f:(fun fs info aa ->
        SortSet.add AddrArray (fold_addrarr fs info aa))
    ~tidarr_f:(fun fs info tt ->
        SortSet.add TidArray (fold_tidarr fs info tt))
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
                 (SortSet.union)
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
        | Skiplist _ -> OpsSet.add SkiplistProp (fold_atom fs info a)
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
    ~set_f:(fun fs info s ->
      match s with
      | PathToSet _ -> OpsSet.add Path2Set (fold_set fs info s)
      | AddrToSet _ -> OpsSet.add Addr2Set (fold_set fs info s)
      | _ -> fold_set fs info s) in

  let ops_fs = F.make_fold
                 F.GenericLiteralFold
                 (ops_fold.atom_f)
                 (fun info -> OpsSet.empty)
                 (OpsSet.union) in

  OpsSet.elements (F.formula_fold ops_fs () phi)



(* NOTE: I am not considering the possibility of having a1=a2 \/ a1=a3 in the formula *)
let rec get_addrs_eqs (phi:formula) : ((addr*addr) list * (addr*addr) list) =
  match phi with
  | F.Literal l   -> get_addrs_eqs_lit l
  | F.And (f1,f2) -> let (es1,is1) = get_addrs_eqs f1 in
                     let (es2,is2) = get_addrs_eqs f2 in
                     (es1@es2, is1@is2)
  | F.Not f       -> let (es,is) = get_addrs_eqs f in (is,es)
  | _             -> ([],[])

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

(*******************************)
(*                             *)
(*     Formula manipulation    *)
(*                             *)
(*******************************)


(* Equality constructor functions for formulas *)
let eq_set (s1:set) (s2:set) : formula =
  F.atom_to_formula (Eq (SetT s1, SetT s2))

let eq_elem (e1:elem) (e2:elem) : formula =
  F.atom_to_formula (Eq (ElemT e1, ElemT e2))

let eq_tid (t1:tid) (t2:tid) : formula =
  F.atom_to_formula (Eq (TidT t1, TidT t2))

let eq_addr (a1:addr) (a2:addr) : formula =
  F.atom_to_formula (Eq (AddrT a1, AddrT a2))

let eq_cell (c1:cell) (c2:cell) : formula =
  F.atom_to_formula (Eq (CellT c1, CellT c2))

let eq_setth (s1:setth) (s2:setth) : formula =
  F.atom_to_formula (Eq (SetThT s1, SetThT s2))

let eq_setelem (s1:setelem) (s2:setelem) : formula =
  F.atom_to_formula (Eq (SetElemT s1, SetElemT s2))

let eq_path (p1:path) (p2:path) : formula =
  F.atom_to_formula (Eq (PathT p1, PathT p2))

let eq_mem (m1:mem) (m2:mem) : formula =
  F.atom_to_formula (Eq (MemT m1, MemT m2))

let eq_int (i1:integer) (i2:integer) : formula =
  F.atom_to_formula (Eq (IntT i1, IntT i2))

let eq_addrarr (aa1:addrarr) (aa2:addrarr) : formula =
  F.atom_to_formula (Eq (AddrArrayT aa1, AddrArrayT aa2))

let eq_tidarr (tt1:tidarr) (tt2:tidarr) : formula =
  F.atom_to_formula (Eq (TidArrayT tt1, TidArrayT tt2))

let eq_term (t1:term) (t2:term) : formula =
  F.atom_to_formula (Eq (t1, t2))

let ineq_set (s1:set) (s2:set) : formula =
  F.atom_to_formula (InEq (SetT s1, SetT s2))

let ineq_elem (e1:elem) (e2:elem) : formula =
  F.atom_to_formula (InEq (ElemT e1, ElemT e2))

let ineq_tid (t1:tid) (t2:tid) : formula =
  F.atom_to_formula (InEq (TidT t1, TidT t2))

let ineq_addr (a1:addr) (a2:addr) : formula =
  F.atom_to_formula (InEq (AddrT a1, AddrT a2))

let ineq_cell (c1:cell) (c2:cell) : formula =
  F.atom_to_formula (InEq (CellT c1, CellT c2))

let ineq_setth (s1:setth) (s2:setth) : formula =
  F.atom_to_formula (InEq (SetThT s1, SetThT s2))

let ineq_setelem (s1:setelem) (s2:setelem) : formula =
  F.atom_to_formula (InEq (SetElemT s1, SetElemT s2))

let ineq_path (p1:path) (p2:path) : formula =
  F.atom_to_formula (InEq (PathT p1, PathT p2))

let ineq_mem (m1:mem) (m2:mem) : formula =
  F.atom_to_formula (InEq (MemT m1, MemT m2))

let ineq_int (i1:integer) (i2:integer) : formula =
  F.atom_to_formula (InEq (IntT i1, IntT i2))

let ineq_addrarr (aa1:addrarr) (aa2:addrarr) : formula =
  F.atom_to_formula (InEq (AddrArrayT aa1, AddrArrayT aa2))

let ineq_tidarr (tt1:tidarr) (tt2:tidarr) : formula =
  F.atom_to_formula (InEq (TidArrayT tt1, TidArrayT tt2))

let ineq_term (t1:term) (t2:term) : formula =
  F.atom_to_formula (InEq (t1, t2))



(*******************************)
(*                             *)
(*   Normalization functions   *)
(*                             *)
(*******************************)




let new_fresh_gen_from_conjformula (cf:conjunctive_formula) : V.fresh_var_gen_t =
  let vars = V.VarSet.fold (fun v s ->
               V.VarIdSet.add (V.id v) s
             ) (varset_from_conj cf) V.VarIdSet.empty in
  V.new_fresh_gen vars


let new_fresh_gen_from_formula (phi:formula) : V.fresh_var_gen_t =
  let vars = V.VarSet.fold (fun v s ->
               V.VarIdSet.add (V.id v) s
             ) (varset phi) V.VarIdSet.empty in
  V.new_fresh_gen vars



(* Normalization *)

type norm_info_t =
  {
    term_map : (term, V.t) Hashtbl.t ;
    processed_term_map : (term, V.t) Hashtbl.t ;
    fresh_gen_info : V.fresh_var_gen_t ;
  }


let new_norm_info_from_formula (phi:formula) : norm_info_t =
  {
    term_map = Hashtbl.create 10 ;
    processed_term_map = Hashtbl.create 10 ;
    fresh_gen_info = new_fresh_gen_from_formula phi ;
  }


let new_norm_info_from_geninfo (fg:V.fresh_var_gen_t) : norm_info_t =
  {
    term_map = Hashtbl.create 10 ;
    processed_term_map = Hashtbl.create 10 ;
    fresh_gen_info = fg ;
  }


let gen_fresh_var (gen:V.fresh_var_gen_t) (s:sort) : V.t =
  V.gen_fresh_var sort_to_str () gen s


let gen_fresh_set_var (info:norm_info_t) : set =
  VarSet (gen_fresh_var info.fresh_gen_info Set)


let gen_fresh_elem_var (info:norm_info_t) : elem =
  VarElem (gen_fresh_var info.fresh_gen_info Elem)


let gen_fresh_tid_var (info:norm_info_t) : tid =
  VarTh (gen_fresh_var info.fresh_gen_info Tid)


let gen_fresh_addr_var (info:norm_info_t) : addr =
  VarAddr (gen_fresh_var info.fresh_gen_info Addr)


let gen_fresh_cell_var (info:norm_info_t) : cell =
  VarCell (gen_fresh_var info.fresh_gen_info Cell)


let gen_fresh_setth_var (info:norm_info_t) : setth =
  VarSetTh (gen_fresh_var info.fresh_gen_info SetTh)


let gen_fresh_setelem_var (info:norm_info_t) : setelem =
  VarSetElem (gen_fresh_var info.fresh_gen_info SetElem)


let gen_fresh_path_var (info:norm_info_t) : path =
  VarPath (gen_fresh_var info.fresh_gen_info Path)


let gen_fresh_mem_var (info:norm_info_t) : mem =
  VarMem (gen_fresh_var info.fresh_gen_info Mem)


let gen_fresh_int_var (info:norm_info_t) : integer =
  VarInt (gen_fresh_var info.fresh_gen_info Int)


let gen_fresh_addrarr_var (info:norm_info_t) : addrarr =
  VarAddrArray (gen_fresh_var info.fresh_gen_info AddrArray)


let gen_fresh_tidarr_var (info:norm_info_t) : tidarr =
  VarTidArray (gen_fresh_var info.fresh_gen_info TidArray)





let make_compatible_term_from_var (t:term) (v:V.t) : term =
  match t with
  | VarT _       -> VarT v
  | SetT _       -> SetT       (VarSet v)
  | ElemT _      -> ElemT      (VarElem v)
  | TidT _      -> TidT      (VarTh v)
  | AddrT _      -> AddrT      (VarAddr v)
  | CellT _      -> CellT      (VarCell v)
  | SetThT _     -> SetThT     (VarSetTh v)
  | SetElemT _   -> SetElemT   (VarSetElem v)
  | PathT _      -> PathT      (VarPath v)
  | MemT _       -> MemT       (VarMem v)
  | IntT _       -> IntT       (VarInt v)
  | AddrArrayT _ -> AddrArrayT (VarAddrArray v)
  | TidArrayT _  -> TidArrayT  (VarTidArray v)
  | VarUpdate _  -> assert false


let term_to_var (t:term) : V.t =
  match t with
  | VarT v -> v
  | SetT       (VarSet v)       -> V.set_sort v Set
  | ElemT      (VarElem v)      -> V.set_sort v Elem
  | TidT       (VarTh v)        -> V.set_sort v Tid
  | AddrT      (VarAddr v)      -> V.set_sort v Addr
  | CellT      (VarCell v)      -> V.set_sort v Cell
  | SetThT     (VarSetTh v)     -> V.set_sort v SetTh
  | SetElemT   (VarSetElem v)   -> V.set_sort v SetElem
  | PathT      (VarPath v)      -> V.set_sort v Path
  | MemT       (VarMem v)       -> V.set_sort v Mem
  | IntT       (VarInt v)       -> V.set_sort v Int
  | AddrArrayT (VarAddrArray v) -> V.set_sort v AddrArray
  | TidArrayT  (VarTidArray v)  -> V.set_sort v TidArray
  | _                           -> raise(No_variable_term t)


let var_to_term (v:V.t) : term =
  match V.sort v with
  | Set       -> SetT       (VarSet        v)
  | Elem      -> ElemT      (VarElem       v)
  | Tid      -> TidT      (VarTh         v)
  | Addr      -> AddrT      (VarAddr       v)
  | Cell      -> CellT      (VarCell       v)
  | SetTh     -> SetThT     (VarSetTh      v)
  | SetElem   -> SetElemT   (VarSetElem    v)
  | Path      -> PathT      (VarPath       v)
  | Mem       -> MemT       (VarMem        v)
  | Int       -> IntT       (VarInt        v)
  | AddrArray -> AddrArrayT (VarAddrArray  v)
  | TidArray  -> TidArrayT  (VarTidArray   v)
  | Bool      -> VarT v
  | Unknown   -> VarT v


let sort_of_term (t:term) : sort =
  match t with
  | SetT       _      -> Set
  | ElemT      _      -> Elem
  | TidT      _      -> Tid
  | AddrT      _      -> Addr
  | CellT      _      -> Cell
  | SetThT     _      -> SetTh
  | SetElemT   _      -> SetElem
  | PathT      _      -> Path
  | MemT       _      -> Mem
  | IntT       _      -> Int
  | AddrArrayT _      -> AddrArray
  | TidArrayT  _      -> AddrArray
  | VarT v            -> V.sort v
  | VarUpdate (v,_,_) -> V.sort v


let rec norm_literal (info:norm_info_t) (l:literal) : formula =
  let append_if_diff (t:term) (v:V.t) : unit =
    if is_var_fold.term_f () t then
      (if (term_to_var t) <> v then Hashtbl.add info.term_map t v)
    else
      Hashtbl.add info.term_map t v in
  let gen_if_not_var (t:term) (s:sort) : V.t =
    let _ = verbl _LONG_INFO "GEN_IF_NOT_VAR FOR TERM: %s\n" (term_to_str t) in
    if is_var_fold.term_f () t then (verbl _LONG_INFO "WAS A VARIABLE\n"; term_to_var t)
    else try
           verbl _LONG_INFO "EXISTING PAIRS:\n";
           Hashtbl.iter (fun t v -> verbl _LONG_INFO "%s ----> %s\n" (term_to_str t) (V.to_str v)) info.term_map;
           try
             Hashtbl.find info.processed_term_map t
           with _ -> Hashtbl.find info.term_map t
         with _ -> begin
                     let v = gen_fresh_var info.fresh_gen_info s in
                     verbl _LONG_INFO "APPENDING A NEW VARIABLE: %s\n" (V.to_str v);
                     append_if_diff t v; v
                   end in

  let norm_map =
    make_map (fun _ _ v -> v)
    ~set_f:(fun fs info s ->
        match s with
        | AddrToSet (m,a,i) -> let i_var = gen_if_not_var (IntT i) Int in
                                 AddrToSet (fs.mem_f fs info m,
                                            fs.addr_f fs info a,
                                            VarInt i_var)
        | _ -> map_set fs info s)
    ~tid_f:(fun fs info t ->
        match t with
        | TidArrRd (tt,i) -> let t_var = gen_if_not_var (TidT t) Tid in
                               VarTh t_var
        | _ -> map_tid fs info t)
    ~addr_f:(fun fs info a ->
        match a with
        | ArrAt (c,i) -> let i_var = gen_if_not_var (IntT i) Int in
                           ArrAt (fs.cell_f fs info c, VarInt i_var)
        | AddrArrRd (aa,i) -> let a_var = gen_if_not_var (AddrT a) Addr in
                                VarAddr a_var
        | _ -> map_addr fs info a)
    ~cell_f:(fun fs info c ->
        match c with
        | MkCell (e,aa,tt,i) -> let c_var = gen_if_not_var (CellT c) Cell in
                                  VarCell c_var
        | CellLockAt (c,i,t) -> let i_var = gen_if_not_var (IntT i) Int in
                                  CellLockAt (fs.cell_f fs info c,
                                              VarInt i_var,
                                              fs.tid_f fs info t)
        | CellUnlockAt (c,i) -> let i_var = gen_if_not_var (IntT i) Int in
                                  CellUnlockAt (fs.cell_f fs info c, VarInt i_var)
        | _ -> map_cell fs info c)
    ~path_f:(fun fs info p ->
        match p with
        | GetPath (m,a1,a2,i) -> let i_var = gen_if_not_var (IntT i) Int in
                                   GetPath (fs.mem_f fs info m,
                                            fs.addr_f fs info a1,
                                            fs.addr_f fs info a2,
                                            VarInt i_var)
        | _ -> map_path fs info p)
    ~int_f:(fun fs info i ->
        match i with
        | IntVal j -> VarInt (gen_if_not_var (IntT i) Int)
        | CellMax c -> let l = gen_if_not_var (IntT i) Int in
                         VarInt l
        | _ -> i)
    ~addrarr_f:(fun fs info aa ->
        match aa with
        | AddrArrayUp (bb,i,a) -> let i_var = gen_if_not_var (IntT i) Int in
                                    AddrArrayUp (fs.addrarr_f fs info bb,
                                                 VarInt i_var,
                                                 fs.addr_f fs info a)
        | _ -> map_addrarr fs info aa)
    ~tidarr_f:(fun fs info tt ->
        match tt with
        | TidArrayUp (yy,i,t) -> let i_var = gen_if_not_var (IntT i) Int in
                                   TidArrayUp (fs.tidarr_f fs info yy,
                                               VarInt i_var,
                                               fs.tid_f fs info t)
        | _ -> map_tidarr fs info tt)
    ~atom_f:(fun fs info a ->
        match a with
        | Reach (m,a1,a2,i,p) -> let i_var = gen_if_not_var (IntT i) Int in
                                   Reach (fs.mem_f fs info m,
                                          fs.addr_f fs info a1,
                                          fs.addr_f fs info a2,
                                          VarInt i_var,
                                          fs.path_f fs info p)
        | Skiplist(m,s,i,a1,a2,es) -> let i_var = gen_if_not_var (IntT i) Int in
                                        Skiplist(fs.mem_f fs info m,
                                                 fs.set_f fs info s,
                                                 VarInt i_var,
                                                 fs.addr_f fs info a1,
                                                 fs.addr_f fs info a2,
                                                 fs.setelem_f fs info es)
        | Less (i1,i2) -> let i1_var = gen_if_not_var (IntT i1) Int in
                          let i2_var = gen_if_not_var (IntT i2) Int in
                            Less (VarInt i1_var, VarInt i2_var)
        | Greater (i1,i2) -> let i1_var = gen_if_not_var (IntT i1) Int in
                             let i2_var = gen_if_not_var (IntT i2) Int in
                               Greater (VarInt i1_var, VarInt i2_var)
        | LessEq (i1,i2) -> let i1_var = gen_if_not_var (IntT i1) Int in
                            let i2_var = gen_if_not_var (IntT i2) Int in
                              LessEq (VarInt i1_var, VarInt i2_var)
        | GreaterEq (i1,i2) -> let i1_var = gen_if_not_var (IntT i1) Int in
                               let i2_var = gen_if_not_var (IntT i2) Int in
                                 GreaterEq (VarInt i1_var, VarInt i2_var)
        (* Equality between cell variable and MkCell *)
        | Eq (CellT (VarCell v), CellT (MkCell (e,aa,tt,i)))
        | Eq (CellT (MkCell (e,aa,tt,i)), CellT (VarCell v)) ->
            let i_var = gen_if_not_var (IntT i) Int in
            let aa_norm = fs.addrarr_f fs info aa in
            let tt_norm = fs.tidarr_f fs info tt in
            let aa' = match aa_norm with
                      | AddrArrayUp _ -> VarAddrArray (gen_if_not_var
                                          (AddrArrayT aa_norm) AddrArray)
                      | _ -> aa_norm in
            let tt' = match tt_norm with
                      | TidArrayUp _ -> VarTidArray (gen_if_not_var
                                          (TidArrayT tt_norm) TidArray)
                      | _ -> tt_norm in
              Eq (CellT (VarCell v), CellT (MkCell(fs.elem_f fs info e, aa',
                                                   tt', VarInt i_var)))
        (* Inequality between cell variable and MkCell *)
        | InEq (CellT (VarCell v), CellT (MkCell (e,aa,tt,i)))
        | InEq (CellT (MkCell (e,aa,tt,i)), CellT (VarCell v)) ->
            let i_var = gen_if_not_var (IntT i) Int in
              InEq (CellT (VarCell v), CellT (MkCell(fs.elem_f fs info e,
                                                     fs.addrarr_f fs info aa,
                                                     fs.tidarr_f fs info tt,
                                                     VarInt i_var)))
        (* Equality between address variable and address array *)
        | Eq (AddrT (VarAddr a), AddrT (AddrArrRd(aa,i)))
        | Eq (AddrT (AddrArrRd(aa,i)), AddrT (VarAddr a)) ->
            let i_var = gen_if_not_var (IntT i) Int in
              Eq (AddrT (VarAddr a),
                  AddrT (AddrArrRd(fs.addrarr_f fs info aa, VarInt i_var)))
        (* Inequality between address variable and address array *)
        | InEq (AddrT (VarAddr a), AddrT (AddrArrRd(aa,i)))
        | InEq (AddrT (AddrArrRd(aa,i)), AddrT (VarAddr a)) ->
            let i_var = gen_if_not_var (IntT i) Int in
              InEq (AddrT (VarAddr a),
                    AddrT (AddrArrRd(fs.addrarr_f fs info aa,VarInt i_var)))
        (* Equality between tid variable  and tids array *)
        | Eq (TidT (VarTh a), TidT (TidArrRd(tt,i)))
        | Eq (TidT (TidArrRd(tt,i)), TidT (VarTh a)) ->
            let i_var = gen_if_not_var (IntT i) Int in
              Eq (TidT (VarTh a),
                  TidT (TidArrRd(fs.tidarr_f fs info tt, VarInt i_var)))
        (* Inequality between tid variable and tids array *)
        | InEq (TidT (VarTh a), TidT (TidArrRd(tt,i)))
        | InEq (TidT (TidArrRd(tt,i)), TidT (VarTh a)) ->
            let i_var = gen_if_not_var (IntT i) Int in
              InEq (TidT (VarTh a),
                    TidT (TidArrRd(fs.tidarr_f fs info tt, VarInt i_var)))
        | PCUpdate (i,t) -> PCUpdate (i, fs.tid_f fs info t)
        | _ -> map_atom fs info a)


  in
  match l with
  | F.Atom a -> F.Literal(F.Atom (norm_map.atom_f () a))
  | F.NegAtom (Skiplist(m,s,i,a1,a2,es)) ->
      let m_var = gen_if_not_var (MemT m) Mem in
      let s_var = gen_if_not_var (SetT s) Set in
      let i_var = gen_if_not_var (IntT i) Int in
      let a1_var = gen_if_not_var (AddrT a1) Addr in
      let a2_var = gen_if_not_var (AddrT a2) Addr in
      let es_var = gen_if_not_var (SetElemT es) SetElem in
      let p = gen_fresh_path_var info in
      let q = gen_fresh_path_var info in
      let r = gen_fresh_set_var info in
      let u = gen_fresh_set_var info in
      let zero = gen_if_not_var (IntT (IntVal 0)) Int in
      let null = gen_if_not_var (AddrT Null) Addr in
      let a = gen_fresh_addr_var info in
      let c = gen_fresh_cell_var info in
      let e = gen_fresh_elem_var info in
      let aa = gen_fresh_addrarr_var info in
      let tt = gen_fresh_tidarr_var info in
      let l1 = gen_fresh_int_var info in
      let l2 = gen_fresh_int_var info in
      let phi_unordered = norm_literal info (F.NegAtom(OrderList
                            (VarMem m_var,VarAddr a1_var,VarAddr a2_var))) in
      let phi_diff = norm_literal info (F.Atom(InEq(SetT (VarSet s_var), SetT r))) in
(*      let phi_a_in_s = norm_literal info (Atom(In(a,VarSet s_var))) in *)
      let phi_not_elems = norm_literal info (F.Atom(InEq(SetElemT (VarSetElem es_var),
                                                         SetElemT(SetToElems(VarSet s_var,VarMem m_var))))) in
      let phi_not_subset = norm_literal info (F.NegAtom(SubsetEq(r,u))) in
        F.disj_list
          [phi_unordered;
           phi_not_elems;
           F.conj_list [eq_path p (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,VarInt zero));
                        eq_set r (PathToSet(p));
                        phi_diff];
           F.Literal(F.Atom(Less(VarInt i_var, VarInt  zero)));
(*
           F.conj_list [phi_a_in_s;
                        eq_cell c (CellAt(VarMem m_var,a));
                        eq_cell c (MkCell(e,aa,tt,l1));
                        Literal(Atom(Less(VarInt i_var,l1)))];
*)
           F.conj_list [ineq_int (VarInt i_var) (VarInt zero);
                        F.Literal(F.Atom(LessEq(VarInt zero,l2)));
                        F.Literal(F.Atom(LessEq(l2,l1)));
                        eq_cell c (CellAt(VarMem m_var,VarAddr a2_var));
                        eq_cell c (MkCell(e,aa,tt,l1));
                        F.Literal(F.Atom(LessEq(l1, (VarInt i_var))));
                        eq_addr a (AddrArrRd(aa,l2));
                        ineq_addr a (VarAddr null)];
           F.conj_list [ineq_int (VarInt i_var) (VarInt zero);
                        F.Literal(F.Atom(LessEq(VarInt zero,l1)));
                        F.Literal(F.Atom(Less(l1,VarInt i_var)));
                        eq_int (l2) (IntAdd(l1,IntVal 1));
                        eq_path (p) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l1));
                        eq_path (q) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr a2_var,l2));
                        eq_set (r) (PathToSet p);
                        eq_set (u) (PathToSet q);
                        phi_not_subset]
          ]
  | F.NegAtom a -> F.Literal(F.NegAtom (norm_map.atom_f () a))


let rec norm_formula (info:norm_info_t) (phi:formula) : formula =
  match phi with
  | F.Literal(F.Atom(InEq(CellT c1, CellT c2))) ->
      norm_formula info (F.Or(ineq_elem (CellData c1) (CellData c2),
                         F.Or(ineq_addrarr (CellArr c1) (CellArr c2),
                         F.Or(ineq_tidarr (CellTids c1) (CellTids c2),
                            ineq_int (CellMax c1) (CellMax c2)))))
  | F.Literal l                 -> norm_literal info l
  | F.True                      -> F.True
  | F.False                     -> F.False
  | F.And (psi1,psi2)           -> F.And (norm_formula info psi1,
                                      norm_formula info psi2)
  | F.Or (psi1,psi2)            -> F.Or (norm_formula info psi1,
                                     norm_formula info psi2)
  | F.Not (F.Literal (F.Atom a))    -> norm_literal info (F.NegAtom a)
  | F.Not (F.Literal (F.NegAtom a)) -> norm_formula info (F.Literal (F.Atom a))
  | F.Not psi                   -> F.Not (norm_formula info psi)
  | F.Implies (psi1,psi2)       -> F.Implies (norm_formula info psi1,
                                          norm_formula info psi2)
  | F.Iff (psi1,psi2)           -> F.Iff (norm_formula info psi1,
                                      norm_formula info psi2)




let normalize (phi:formula) : formula =
  verblstr LeapVerbose._LONG_INFO
    (Interface.Msg.info "NEW FORMULA TO NORMALIZE" (formula_to_str phi));
  (* Create a new normalization *)
  let norm_info = new_norm_info_from_formula phi in
  (* Process the original formula *)
  let phi' = norm_formula norm_info (F.nnf phi) in
  (* Normalize all remaining literals stored in the normalization table *)
  verbl _LONG_INFO "WILL NORMALIZE REMAINING ELEMENTS";
  let lit_list = ref [] in
  while (Hashtbl.length norm_info.term_map > 0) do
    Hashtbl.iter (fun t v ->
      begin
        match t with
        | IntT (CellMax _) -> ()
        | _ -> begin
                 Hashtbl.add norm_info.processed_term_map t v;
                 verbl _LONG_INFO "PROCESSING: %s ----> %s\n" (term_to_str t) (V.to_str v);
                 let l = F.Atom (Eq (make_compatible_term_from_var t v, t)) in
                 let new_l = norm_literal norm_info l in
                 verblstr LeapVerbose._LONG_INFO
                   (Interface.Msg.info "REMAINING TSL LITERAL TO NORMALIZE" (formula_to_str new_l));
                 let lit_to_add = match new_l with
                                  | F.Literal(F.Atom(Eq(t1,t2)))
                                  | F.Literal(F.NegAtom(InEq(t1,t2))) ->
                                      if t1 <> t2 then new_l else F.Literal l
                                  | _ -> new_l in
                 lit_list := lit_to_add :: !lit_list
               end
      end;
      Hashtbl.remove norm_info.term_map t
    ) norm_info.term_map;
  done;
  if !lit_list = [] then
    phi'
  else
    F.And (F.conj_list !lit_list, phi')


(**************************)
(**  TERMS SUBSTITUTION  **)
(**************************)

let check_well_defined_replace_table (tbl:(term, term) Hashtbl.t) : unit =
  Hashtbl.iter (fun a b ->
    match (a,b) with
    | (VarT _,  VarT _)            -> ()
    | (SetT _,  SetT _)            -> ()
    | (ElemT _, ElemT _)           -> ()
    | (TidT _, TidT _)             -> ()
    | (AddrT _, AddrT _)           -> ()
    | (CellT _, CellT _)           -> ()
    | (SetThT _, SetThT _)         -> ()
    | (SetElemT _, SetElemT _)     -> ()
    | (PathT _, PathT _)           -> ()
    | (MemT _, MemT _)             -> ()
    | (IntT _, IntT _)             -> ()
    | (AddrArrayT _, AddrArrayT _) -> ()
    | (TidArrayT _, TidArrayT _)   -> ()
    | (VarUpdate _, VarUpdate _)   -> ()
    | _ -> raise(Incompatible_replacement(a,b))
  ) tbl



let rec replace_terms_in_vars (tbl:(term,term) Hashtbl.t) (v:V.t) : V.t =
  try
    match Hashtbl.find tbl (VarT v) with
    | VarT v -> v
    | _ -> assert false
  with _ -> v


let replace_terms_map =
  make_map (fun _ tbl v -> replace_terms_in_vars tbl v)
  ~addrarr_f:(fun fs tbl aa ->
      try
        match Hashtbl.find tbl (AddrArrayT aa) with
        | AddrArrayT aa' -> aa'
        | _ -> assert false
      with _ -> map_addrarr fs tbl aa)
  ~tidarr_f:(fun fs tbl tt ->
      try
        match Hashtbl.find tbl (TidArrayT tt) with
        | TidArrayT tt' -> tt'
        | _ -> assert false
      with _ -> map_tidarr fs tbl tt)
  ~set_f:(fun fs tbl s ->
      try
        match Hashtbl.find tbl (SetT s) with
        | SetT s' -> s'
        | _ -> assert false
      with _ -> map_set fs tbl s)
  ~addr_f:(fun fs tbl a ->
      try
        match Hashtbl.find tbl (AddrT a) with
        | AddrT a' -> a'
        | _ -> assert false
      with _ -> map_addr fs tbl a)
  ~elem_f:(fun fs tbl e ->
      try
        match Hashtbl.find tbl (ElemT e) with
        | ElemT e' -> e'
        | _ -> assert false
      with _ -> map_elem fs tbl e)
  ~tid_f:(fun fs tbl t ->
      try
        match Hashtbl.find tbl (TidT t) with
        | TidT t' -> t'
        | _ -> assert false
      with _ -> map_tid fs tbl t)
  ~cell_f:(fun fs tbl c ->
      try
        match Hashtbl.find tbl (CellT c) with
        | CellT c' -> c'
        | _ -> assert false
      with _ -> map_cell fs tbl c)
  ~setth_f:(fun fs tbl st ->
      try
        match Hashtbl.find tbl (SetThT st) with
        | SetThT st' -> st'
        | _ -> assert false
      with _ -> map_setth fs tbl st)
  ~setelem_f:(fun fs tbl se ->
      try
        match Hashtbl.find tbl (SetElemT se) with
        | SetElemT se' -> se'
        | _ -> assert false
      with _ -> map_setelem fs tbl se)
  ~path_f:(fun fs tbl p ->
      try
        match Hashtbl.find tbl (PathT p) with
        | PathT p' -> p'
        | _ -> assert false
      with _ -> map_path fs tbl p)
  ~mem_f:(fun fs tbl m ->
      try
        match Hashtbl.find tbl (MemT m) with
        | MemT m' -> m'
        | _ -> assert false
      with _ -> map_mem fs tbl m)
  ~int_f:(fun fs tbl i ->
      try
        match Hashtbl.find tbl (IntT i) with
        | IntT i' -> i'
        | _ -> assert false
      with _ -> map_int fs tbl i)


let replace_fs = F.make_trans F.GenericLiteralTrans replace_terms_map.atom_f

let replace_terms_literal (tbl:(term,term) Hashtbl.t) (l:literal) : literal =
  F.literal_trans replace_fs tbl l

let replace_terms_formula_aux (tbl:(term,term) Hashtbl.t) (phi:formula) : formula =
  F.formula_trans replace_fs tbl phi


let replace_terms (tbl:(term, term) Hashtbl.t) (phi:formula) : formula =
  check_well_defined_replace_table tbl;
  replace_terms_formula_aux tbl phi


(* Vocabulary to variable conversion *)
let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)


let param_map =
  make_map (fun _ pfun v -> V.set_param v (pfun (Some v)))

let param_fs =
  F.make_trans F.GenericLiteralTrans param_map.atom_f


(**********************  Generic Expression Functions  ********************)

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

