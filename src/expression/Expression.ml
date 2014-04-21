open Printf
open LeapLib
open LeapVerbose


type sort =
    Set
  | Elem
  | Tid
  | Addr
  | Cell
  | SetTh
  | SetInt
  | SetElem
  | Path
  | Mem
  | Bool
  | Int
  | Array
  | AddrArray
  | TidArray
  | Unknown

type var_nature =
  | RealVar
  | GhostVar

type var_info_t =
  {
    nature : var_nature;
  }


module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = var_info_t
  end )


module F = Formula


type logic_op_t = AndOp | OrOp | ImpliesOp | IffOp | NotOp | NoneOp

type pc_t = int


type initVal_t =
  | Equality of term
  | Condition of formula


and term =
  | VarT          of V.t
  | SetT          of set
  | ElemT         of elem
  | TidT          of tid
  | AddrT         of addr
  | CellT         of cell
  | SetThT        of setth
  | SetIntT       of setint
  | SetElemT      of setelem
  | PathT         of path
  | MemT          of mem
  | IntT          of integer
  | ArrayT        of arrays
  | AddrArrayT    of addrarr
  | TidArrayT     of tidarr

and eq =          term * term

and diseq =       term * term

and arrays =
  | VarArray      of V.t
  | ArrayUp       of arrays * tid * expr_t

and addrarr =
  | VarAddrArray  of V.t
  | AddrArrayUp   of addrarr * integer * addr
  | CellArr       of cell

and tidarr =
  | VarTidArray   of V.t
  | TidArrayUp    of tidarr * integer * tid
  | CellTids      of cell

and integer =
  | IntVal        of int
  | VarInt        of V.t
  | IntNeg        of integer
  | IntAdd        of integer * integer
  | IntSub        of integer * integer
  | IntMul        of integer * integer
  | IntDiv        of integer * integer
  | IntArrayRd    of arrays * tid
  | IntSetMin     of setint
  | IntSetMax     of setint
  | CellMax       of cell
  | HavocLevel

and set =
  | VarSet        of V.t
  | EmptySet
  | Singl         of addr
  | Union         of set * set
  | Intr          of set * set
  | Setdiff       of set * set
  | PathToSet     of path
  | AddrToSet     of mem * addr
  | AddrToSetAt   of mem * addr * integer
  | SetArrayRd    of arrays * tid

and tid =
  | VarTh         of V.t
  | NoTid
  | CellLockId    of cell
  | CellLockIdAt  of cell * integer
  | TidArrayRd    of arrays * tid
  | TidArrRd      of tidarr * integer

and elem =
  | VarElem           of V.t
  | CellData          of cell
  | ElemArrayRd       of arrays * tid
  | HavocListElem
  | HavocSkiplistElem
  | LowestElem
  | HighestElem

and addr =
  | VarAddr       of V.t
  | Null
  | Next          of cell
  | NextAt        of cell * integer
  | ArrAt         of cell * integer
  | FirstLocked   of mem * path
  | FirstLockedAt of mem * path * integer
  | AddrArrayRd   of arrays * tid
  | AddrArrRd     of addrarr * integer

and cell =
  | VarCell       of V.t
  | Error
  | MkCell        of elem * addr * tid
  | MkSLKCell     of elem * addr list * tid list
  | MkSLCell      of elem * addrarr * tidarr * integer
  | CellLock      of cell * tid
  | CellLockAt    of cell * integer * tid
  | CellUnlock    of cell
  | CellUnlockAt  of cell * integer
  | CellAt        of mem * addr
  | CellArrayRd   of arrays * tid
  | UpdCellAddr   of cell * integer * addr

and setth =
  | VarSetTh      of V.t
  | EmptySetTh
  | SinglTh       of tid
  | UnionTh       of setth * setth
  | IntrTh        of setth * setth
  | SetdiffTh     of setth * setth
  | SetThArrayRd  of arrays * tid

and setint =
  | VarSetInt     of V.t
  | EmptySetInt
  | SinglInt      of integer
  | UnionInt      of setint * setint
  | IntrInt       of setint * setint
  | SetdiffInt    of setint * setint
  | SetIntArrayRd of arrays * tid

and setelem =
  | VarSetElem     of V.t
  | EmptySetElem
  | SinglElem      of elem
  | UnionElem      of setelem * setelem
  | IntrElem       of setelem * setelem
  | SetdiffElem    of setelem * setelem
  | SetToElems     of set * mem
  | SetElemArrayRd of arrays * tid

and path =
  | VarPath       of V.t
  | Epsilon
  | SimplePath    of addr
  | GetPath       of mem * addr * addr
  | GetPathAt     of mem * addr * addr * integer
  | PathArrayRd   of arrays * tid

and mem =
  | VarMem        of V.t
  | Update        of mem * addr * cell
  | MemArrayRd    of arrays * tid

and atom =
  | Append        of path * path * path
  | Reach         of mem * addr * addr * path
  | ReachAt       of mem * addr * addr * integer * path
  | OrderList     of mem * addr * addr
  | Skiplist      of mem * set * integer * addr * addr * setelem
  | In            of addr * set
  | SubsetEq      of set * set
  | InTh          of tid * setth
  | SubsetEqTh    of setth * setth
  | InInt         of integer * setint
  | SubsetEqInt   of setint * setint
  | InElem        of elem * setelem
  | SubsetEqElem  of setelem * setelem
  | Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | LessElem      of elem * elem
  | GreaterElem   of elem * elem
  | Eq            of eq
  | InEq          of diseq
  | BoolVar       of V.t
  | BoolArrayRd   of arrays * tid
  | PC            of pc_t * V.shared_or_local * bool
  | PCUpdate      of pc_t * tid
  | PCRange       of pc_t * pc_t * V.shared_or_local * bool

and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula

and expr_t =
  | Term          of term
  | Formula       of formula

(* CHANGES: I think it will be better to move this to a "substitution module"
            parametrized by a theory. Maybe a fold function *)
and tid_subst_t = (tid * tid) list

(* CHANGES: fol_mode maybe also another module parametrized by a theory *)
type fol_mode_t =
  | PCOnly
  | VarsOnly
  | PCVars

type fol_ops_t =
  {
    fol_pc : bool;
    fol_var : V.t -> V.t;
  }


module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )


module TermSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = term
  end )


module SortSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = sort
  end )


module FormulaSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = formula
  end )


module PosSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = pc_t
  end )




(* Exceptions *)
exception Invalid_argument
exception No_variable_term of string
exception Impossible_to_convert of tid
exception Incompatible_assignment of term * expr_t
exception Not_implemented of string
exception Not_tid_var of tid





(* Configuration *)
let defCountVar : integer =
  VarInt (V.build Conf.defCountAbs_name Int false V.Shared V.GlobalScope
          {nature = RealVar})


(* The heap *)
let heap : mem =
  VarMem (V.build Conf.heap_name Mem false V.Shared V.GlobalScope
          {nature = RealVar})

(*
(* Fresh auxiliary variables *)
let fresh_cell = VarCell { id = fresh_cell_name;
                          sort = Cell;
                          is_primed = false;
                          parameter = Shared;
                          scope = GlobalScope;
                          nature = RealVar; }
*)



(* VARIABLE FUNCTIONS *)
let build_var ?(fresh=false)
              ?(nature=RealVar)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
  V.build id s pr th p {nature=nature;} ~fresh:fresh


let var_nature (v:V.t) : var_nature =
  (V.info v).nature

(* TUKA *)
let is_pc_var (v:V.t) : bool =
  String.sub (V.id v) 0 3 = "pc_"


let build_global_var (id:V.id) (s:sort) : V.t =
  build_var id s false V.Shared V.GlobalScope


let build_num_tid_var (i:int) : V.t =
  build_global_var ("k" ^ string_of_int i) Tid



(* PRIMING FUNCTIONS *)

(* Priming functions used for thread identifiers *)
let rec is_primed_array (a:arrays) : bool =
  match a with
    VarArray v       -> V.is_primed v
  | ArrayUp (a',_,_) -> is_primed_array a'

let rec is_primed_addrarray (a:addrarr) : bool =
  match a with
    VarAddrArray v       -> V.is_primed v
  | AddrArrayUp (a',_,_) -> is_primed_addrarray a'
  | CellArr c            -> false

let rec is_primed_tidarray (a:tidarr) : bool =
  match a with
    VarTidArray v       -> V.is_primed v
  | TidArrayUp (a',_,_) -> is_primed_tidarray a'
  | CellTids c            -> false

let is_primed_tid (th:tid) : bool =
  match th with
    VarTh v           -> V.is_primed v
  | NoTid            -> false
  | CellLockId _      -> false
  | CellLockIdAt _    -> false
  | TidArrayRd (a,_) -> is_primed_array a
  | TidArrRd (a,_)   -> is_primed_tidarray a
  (* FIX: Propagate the query inside cell??? *)


let var_base_info = V.unparam>>V.unprime

(* Priming functions used for thread identifiers *)

let rec priming_option_tid (pr:bool)
                           (prime_set:(V.VarSet.t option * bool))
                           (expr:V.shared_or_local) : V.shared_or_local =
  (* This statement primes the thread parameter of expressions *)
  (* Option.lift (priming_th_t pr) expr *)
  (* This statement leaves the thread parameter unprimed *)
  expr


let priming_variable (pr:bool)
                     (prime_set:(V.VarSet.t option * bool))
                     (v:V.t) : V.t =
  let v' = if pr then V.prime v else V.unprime v in
	match (fst prime_set) with
	| None   -> v'
(* DO NOT ERASE: This may be needed!!!! *)
  | Some s -> if (V.VarSet.mem (V.set_param v V.Shared) s ||
                  V.VarSet.mem (v) s                  ) then v' else v
(*      | Some s -> if V.VarSet.mem v s then v' else v *)


let rec priming_term (pr:bool)
                     (prime_set:(V.VarSet.t option * bool))
                     (expr:term) : term =
  match expr with
    VarT v            -> VarT       (priming_variable   pr prime_set v)
  | SetT(set)         -> SetT       (priming_set        pr prime_set set)
  | AddrT(addr)       -> AddrT      (priming_addr       pr prime_set addr)
  | ElemT(elem)       -> ElemT      (priming_elem       pr prime_set elem)
  | TidT(th)          -> TidT       (priming_tid        pr prime_set th)
  | CellT(cell)       -> CellT      (priming_cell       pr prime_set cell)
  | SetThT(setth)     -> SetThT     (priming_setth      pr prime_set setth)
  | SetIntT(setint)   -> SetIntT    (priming_setint     pr prime_set setint)
  | SetElemT(setelem) -> SetElemT   (priming_setelem    pr prime_set setelem)
  | PathT(path)       -> PathT      (priming_path       pr prime_set path)
  | MemT(mem)         -> MemT       (priming_mem        pr prime_set mem)
  | IntT(i)           -> IntT       (priming_int        pr prime_set i)
  | ArrayT(arr)       -> ArrayT     (priming_array      pr prime_set arr)
  | AddrArrayT(arr)   -> AddrArrayT (priming_addrarray  pr prime_set arr)
  | TidArrayT(arr)    -> TidArrayT  (priming_tidarray   pr prime_set arr)


and priming_expr (pr:bool) (prime_set:(V.VarSet.t option * bool)) (expr:expr_t) : expr_t =
  match expr with
    Term t    -> Term (priming_term pr prime_set t)
  | Formula b -> Formula (priming_formula pr prime_set b)


and priming_array (pr:bool) (prime_set:(V.VarSet.t option * bool)) (expr:arrays) : arrays =
  match expr with
    VarArray v       -> VarArray (priming_variable pr prime_set v)
  | ArrayUp(arr,t,e) -> ArrayUp  (priming_array pr prime_set arr,
                                  priming_tid   pr prime_set t,
                                  priming_expr  pr prime_set e)

and priming_addrarray (pr:bool) (prime_set:(V.VarSet.t option * bool)) (expr:addrarr)
      : addrarr =
  match expr with
    VarAddrArray v       -> VarAddrArray (priming_variable pr prime_set v)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp  (priming_addrarray pr prime_set arr,
                                          priming_int   pr prime_set i,
                                          priming_addr  pr prime_set a)
  | CellArr c            -> CellArr (priming_cell pr prime_set c)

and priming_tidarray (pr:bool) (prime_set:(V.VarSet.t option * bool)) (expr:tidarr)
      : tidarr =
  match expr with
    VarTidArray v       -> VarTidArray (priming_variable pr prime_set v)
  | TidArrayUp(arr,i,t) -> TidArrayUp  (priming_tidarray pr prime_set arr,
                                          priming_int  pr prime_set i,
                                          priming_tid  pr prime_set t)
  | CellTids c            -> CellTids (priming_cell pr prime_set c)

and priming_set (pr:bool) (prime_set:(V.VarSet.t option * bool)) (e:set) : set =
  match e with
    VarSet v            -> VarSet (priming_variable pr prime_set v)
  | EmptySet            -> EmptySet
  | Singl(addr)         -> Singl(priming_addr pr prime_set addr)
  | Union(s1,s2)        -> Union(priming_set pr prime_set s1,
                                 priming_set pr prime_set s2)
  | Intr(s1,s2)         -> Intr(priming_set pr prime_set s1,
                                priming_set pr prime_set s2)
  | Setdiff(s1,s2)      -> Setdiff(priming_set pr prime_set s1,
                                   priming_set pr prime_set s2)
  | PathToSet(path)     -> PathToSet(priming_path pr prime_set path)
  | AddrToSet(mem,addr) -> AddrToSet(priming_mem pr prime_set mem,
                                     priming_addr pr prime_set addr)
  | AddrToSetAt(mem,a,l)-> AddrToSetAt(priming_mem pr prime_set mem,
                                       priming_addr pr prime_set a,
                                       priming_int pr prime_set l)
  | SetArrayRd(arr,t)   -> SetArrayRd(priming_array pr prime_set arr,
                                      priming_tid pr prime_set t)


and priming_addr (pr:bool) (prime_set:(V.VarSet.t option * bool)) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr (priming_variable pr prime_set v)
  | Null                      -> Null
  | Next(cell)                -> Next(priming_cell pr prime_set cell)
  | NextAt(cell,l)            -> NextAt(priming_cell pr prime_set cell,
                                        priming_int pr prime_set l)
  | ArrAt(cell,l)             -> ArrAt(priming_cell pr prime_set cell,
                                        priming_int pr prime_set l)
  | FirstLocked(mem,path)     -> FirstLocked(priming_mem pr prime_set mem,
                                             priming_path pr prime_set path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(priming_mem pr prime_set mem,
                                               priming_path pr prime_set path,
                                               priming_int pr prime_set l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(priming_array pr prime_set arr,
                                             priming_tid pr prime_set t)
  | AddrArrRd(arr,l)          -> AddrArrRd(priming_addrarray pr prime_set arr,
                                           priming_int pr prime_set l)

and priming_elem (pr:bool) (prime_set:(V.VarSet.t option * bool)) (e:elem) : elem =
  match e with
    VarElem v          -> VarElem (priming_variable pr prime_set v)
  | CellData(cell)     -> CellData(priming_cell pr prime_set cell)
  | ElemArrayRd(arr,t) -> ElemArrayRd(priming_array pr prime_set arr,
                                      priming_tid pr prime_set t)

  | HavocListElem      -> HavocListElem
  | HavocSkiplistElem  -> HavocSkiplistElem
  | LowestElem         -> LowestElem
  | HighestElem        -> HighestElem


and priming_tid (pr:bool) (prime_set:(V.VarSet.t option * bool)) (th:tid) : tid =
  match th with
    VarTh v              -> VarTh (priming_variable pr prime_set v)
  | NoTid               -> NoTid
  | CellLockId(cell)     -> CellLockId(priming_cell pr prime_set cell)
  | CellLockIdAt(cell,l) -> CellLockIdAt(priming_cell pr prime_set cell,
                                         priming_int pr prime_set l)
  | TidArrayRd(arr,t)   -> TidArrayRd(priming_array pr prime_set arr,
                                      priming_tid pr prime_set t)
  | TidArrRd(arr,l)     -> TidArrRd(priming_tidarray pr prime_set arr,
                                      priming_int pr prime_set l)


and priming_cell (pr:bool) (prime_set:(V.VarSet.t option * bool)) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (priming_variable pr prime_set v)
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(priming_elem pr prime_set data,
                                     priming_addr pr prime_set addr,
                                     priming_tid pr prime_set th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(priming_elem pr prime_set data,
                                        List.map (priming_addr pr prime_set) aa,
                                        List.map (priming_tid pr prime_set) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(priming_elem pr prime_set data,
                                       priming_addrarray pr prime_set aa,
                                       priming_tidarray pr prime_set ta,
                                       priming_int pr prime_set l)
  | CellLock(cell, t)      -> CellLock(priming_cell pr prime_set cell,
                                       priming_tid pr prime_set t)
  | CellLockAt(cell,l, t)  -> CellLockAt(priming_cell pr prime_set cell,
                                         priming_int pr prime_set l,
                                         priming_tid pr prime_set t)
  | CellUnlock(cell)       -> CellUnlock(priming_cell pr prime_set cell)
  | CellUnlockAt(cell,l)   -> CellUnlockAt(priming_cell pr prime_set cell,
                                           priming_int pr prime_set l)
  | CellAt(mem,addr)       -> CellAt(priming_mem pr prime_set mem,
                                     priming_addr pr prime_set addr)
  | CellArrayRd(arr,t)     -> CellArrayRd(priming_array pr prime_set arr,
                                          priming_tid pr prime_set t)
  | UpdCellAddr(c,i,a)     -> UpdCellAddr(priming_cell pr prime_set c,
                                          priming_int pr prime_set i,
                                          priming_addr pr prime_set a)


and priming_setth (pr:bool) (prime_set:(V.VarSet.t option * bool)) (s:setth) : setth =
  match s with
    VarSetTh v          -> VarSetTh (priming_variable pr prime_set v)
  | EmptySetTh          -> EmptySetTh
  | SinglTh(th)         -> SinglTh(priming_tid pr prime_set th)
  | UnionTh(s1,s2)      -> UnionTh(priming_setth pr prime_set s1,
                                   priming_setth pr prime_set s2)
  | IntrTh(s1,s2)       -> IntrTh(priming_setth pr prime_set s1,
                                  priming_setth pr prime_set s2)
  | SetdiffTh(s1,s2)    -> SetdiffTh(priming_setth pr prime_set s1,
                                     priming_setth pr prime_set s2)
  | SetThArrayRd(arr,t) -> SetThArrayRd(priming_array pr prime_set arr,
                                        priming_tid pr prime_set t)


and priming_setint (pr:bool) (prime_set:(V.VarSet.t option * bool)) (s:setint) : setint =
  match s with
    VarSetInt v          -> VarSetInt (priming_variable pr prime_set v)
  | EmptySetInt          -> EmptySetInt
  | SinglInt(th)         -> SinglInt(priming_int pr prime_set th)
  | UnionInt(s1,s2)      -> UnionInt(priming_setint pr prime_set s1,
                                     priming_setint pr prime_set s2)
  | IntrInt(s1,s2)       -> IntrInt(priming_setint pr prime_set s1,
                                    priming_setint pr prime_set s2)
  | SetdiffInt(s1,s2)    -> SetdiffInt(priming_setint pr prime_set s1,
                                       priming_setint pr prime_set s2)
  | SetIntArrayRd(arr,t) -> SetIntArrayRd(priming_array pr prime_set arr,
                                          priming_tid pr prime_set t)


and priming_setelem (pr:bool) (prime_set:(V.VarSet.t option * bool)) (s:setelem) : setelem =
  match s with
    VarSetElem v          -> VarSetElem (priming_variable pr prime_set v)
  | EmptySetElem          -> EmptySetElem
  | SinglElem(e)          -> SinglElem(priming_elem pr prime_set e)
  | UnionElem(s1,s2)      -> UnionElem(priming_setelem pr prime_set s1,
                                       priming_setelem pr prime_set s2)
  | IntrElem(s1,s2)       -> IntrElem(priming_setelem pr prime_set s1,
                                      priming_setelem pr prime_set s2)
  | SetdiffElem(s1,s2)    -> SetdiffElem(priming_setelem pr prime_set s1,
                                         priming_setelem pr prime_set s2)
  | SetToElems(s,m)       -> SetToElems(priming_set pr prime_set s,
                                        priming_mem pr prime_set m)
  | SetElemArrayRd(arr,t) -> SetElemArrayRd(priming_array pr prime_set arr,
                                            priming_tid pr prime_set t)

and priming_path (pr:bool) (prime_set:(V.VarSet.t option * bool)) (p:path) : path =
  match p with
    VarPath v                        -> VarPath (priming_variable pr prime_set v)
  | Epsilon                          -> Epsilon
  | SimplePath(addr)                 -> SimplePath(priming_addr pr prime_set addr)
  | GetPath(mem,add_from,add_to)     -> GetPath(priming_mem pr prime_set mem,
                                                priming_addr pr prime_set add_from,
                                                priming_addr pr prime_set add_to)
  | GetPathAt(mem,add_from,add_to,l) -> GetPathAt(priming_mem pr prime_set mem,
                                                  priming_addr pr prime_set add_from,
                                                  priming_addr pr prime_set add_to,
                                                  priming_int pr prime_set l)
  | PathArrayRd(arr,t)               -> PathArrayRd(priming_array pr prime_set arr,
                                                    priming_tid pr prime_set t)


and priming_mem (pr:bool) (prime_set:(V.VarSet.t option * bool)) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem(priming_variable pr prime_set v)
  | Update(mem,add,cell) -> Update(priming_mem pr prime_set mem,
                                   priming_addr pr prime_set add,
                                   priming_cell pr prime_set cell)
  | MemArrayRd(arr,t)    -> MemArrayRd(priming_array pr prime_set arr,
                                       priming_tid pr prime_set t)


and priming_int (pr:bool) (prime_set:(V.VarSet.t option * bool)) (i:integer) : integer =
  match i with
    IntVal(i)         -> IntVal(i)
  | VarInt v          -> VarInt(priming_variable pr prime_set v)
  | IntNeg(i)         -> IntNeg(priming_int pr prime_set i)
  | IntAdd(i1,i2)     -> IntAdd(priming_int pr prime_set i1,
                                priming_int pr prime_set i2)
  | IntSub(i1,i2)     -> IntSub(priming_int pr prime_set i1,
                                priming_int pr prime_set i2)
  | IntMul(i1,i2)     -> IntMul(priming_int pr prime_set i1,
                                priming_int pr prime_set i2)
  | IntDiv(i1,i2)     -> IntDiv(priming_int pr prime_set i1,
                                priming_int pr prime_set i2)
  | IntArrayRd(arr,t) -> IntArrayRd(priming_array pr prime_set arr,
                                    priming_tid pr prime_set t)
  | IntSetMin(s)      -> IntSetMin(priming_setint pr prime_set s)
  | IntSetMax(s)      -> IntSetMax(priming_setint pr prime_set s)
  | CellMax c         -> CellMax (priming_cell pr prime_set c)
  | HavocLevel        -> HavocLevel



and priming_atom (pr:bool) (prime_set:(V.VarSet.t option * bool)) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                -> Append(priming_path pr prime_set p1,
                                                priming_path pr prime_set p2,
                                                priming_path pr prime_set pres)
  | Reach(h,add_from,add_to,p)        -> Reach(priming_mem pr prime_set h,
                                               priming_addr pr prime_set add_from,
                                               priming_addr pr prime_set add_to,
                                               priming_path pr prime_set p)
  | ReachAt(h,a_from,a_to,l,p)        -> ReachAt(priming_mem pr prime_set h,
                                                 priming_addr pr prime_set a_from,
                                                 priming_addr pr prime_set a_to,
                                                 priming_int pr prime_set l,
                                                 priming_path pr prime_set p)
  | OrderList(h,a_from,a_to)          -> OrderList(priming_mem pr prime_set h,
                                                   priming_addr pr prime_set a_from,
                                                   priming_addr pr prime_set a_to)
  | Skiplist(h,s,l,a_from,a_to,elems) -> Skiplist(priming_mem pr prime_set h,
                                                  priming_set pr prime_set s,
                                                  priming_int pr prime_set l,
                                                  priming_addr pr prime_set a_from,
                                                  priming_addr pr prime_set a_to,
                                                  priming_setelem pr prime_set elems)
  | In(a,s)                           -> In(priming_addr pr prime_set a,
                                            priming_set pr prime_set s)
  | SubsetEq(s_in,s_out)              -> SubsetEq(priming_set pr prime_set s_in,
                                                  priming_set pr prime_set s_out)
  | InTh(th,s)                        -> InTh(priming_tid pr prime_set th,
                                              priming_setth pr prime_set s)
  | SubsetEqTh(s_in,s_out)            -> SubsetEqTh(priming_setth pr prime_set s_in,
                                                    priming_setth pr prime_set s_out)
  | InInt(i,s)                        -> InInt(priming_int pr prime_set i,
                                               priming_setint pr prime_set s)
  | SubsetEqInt(s_in,s_out)           -> SubsetEqInt(priming_setint pr prime_set s_in,
                                                     priming_setint pr prime_set s_out)
  | InElem(e,s)                       -> InElem(priming_elem pr prime_set e,
                                                priming_setelem pr prime_set s)
  | SubsetEqElem(s_in,s_out)          -> SubsetEqElem(priming_setelem pr prime_set s_in,
                                                      priming_setelem pr prime_set s_out)
  | Less(i1,i2)                       -> Less(priming_int pr prime_set i1,
                                              priming_int pr prime_set i2)
  | Greater(i1,i2)                    -> Greater(priming_int pr prime_set i1,
                                                 priming_int pr prime_set i2)
  | LessEq(i1,i2)                     -> LessEq(priming_int pr prime_set i1,
                                                priming_int pr prime_set i2)
  | LessTid(t1,t2)                    -> LessTid(priming_tid pr prime_set t1,
                                                 priming_tid pr prime_set t2)
  | LessElem(e1,e2)                   -> LessElem(priming_elem pr prime_set e1,
                                                  priming_elem pr prime_set e2)
  | GreaterElem(e1,e2)                -> GreaterElem(priming_elem pr prime_set e1,
                                                     priming_elem pr prime_set e2)
  | GreaterEq(i1,i2)                  -> GreaterEq(priming_int pr prime_set i1,
                                                   priming_int pr prime_set i2)
  | Eq(exp)                           -> Eq(priming_eq pr prime_set exp)
  | InEq(exp)                         -> InEq(priming_ineq pr prime_set exp)
  | BoolVar v                         -> BoolVar (priming_variable pr prime_set v)
  | BoolArrayRd (a,t)                 -> BoolArrayRd (priming_array pr prime_set a,
                                                      priming_tid pr prime_set t)
	| PC (pc,t,_)                       -> PC (pc, t, snd prime_set)
	| PCUpdate (pc,t)                   -> PCUpdate (pc,t)
	| PCRange (pc1,pc2,t,_)             -> PCRange (pc1, pc2, t, snd prime_set)


and priming_eq (pr:bool) (prime_set:(V.VarSet.t option * bool)) ((t1,t2):eq) : eq =
  (priming_term pr prime_set t1, priming_term pr prime_set t2)


and priming_ineq (pr:bool) (prime_set:(V.VarSet.t option * bool)) ((t1,t2):diseq) : diseq =
	(priming_term pr prime_set t1, priming_term pr prime_set t2)


and priming_fs () = Formula.make_trans
                      Formula.GenericLiteralTrans
                      (fun (pr,prime_set) a -> priming_atom pr prime_set a)

and priming_formula (pr:bool) (prime_set:(V.VarSet.t option * bool)) (phi:formula) =
  Formula.formula_trans (priming_fs()) (pr,prime_set) phi

(*
and priming_literal (pr:bool) (prime_set:V.VarSet.t option) (l:literal) : 
  literal=
  match l with
    Atom a    -> Atom (priming_atom pr prime_set a)
  | NegAtom a -> NegAtom (priming_atom pr prime_set a)


and priming_conjunctive_formula (pr:bool)
                                (prime_set:V.VarSet.t option)
                                (cf:conjunctive_formula) : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (priming_literal pr prime_set) ls)


and priming_formula (pr:bool) (prime_set:V.VarSet.t option) (phi:formula) : 
  formula =
  match phi with
    Literal(lit)         -> Literal(priming_literal pr prime_set lit)
  | True                 -> True
  | False                -> False
  | And(f1,f2)           -> And(priming_formula pr prime_set f1,
                                priming_formula pr prime_set f2)
  | Or(f1,f2)            -> Or(priming_formula pr prime_set f1,
                               priming_formula pr prime_set f2)
  | Not(f)               -> Not(priming_formula pr prime_set f)
  | Implies(f1,f2)       -> Implies(priming_formula pr prime_set f1,
                                    priming_formula pr prime_set f2)
  | Iff (f1,f2)          -> Iff(priming_formula pr prime_set f1,
                                priming_formula pr prime_set f2)

*)

(* exported priming functions *)

let prime_addr (a:addr) : addr   =  priming_addr true    (None, true) a
let unprime_addr (a:addr) : addr =  priming_addr false (None, false) a
let prime_elem (e:elem) : elem   =  priming_elem true    (None, true) e
let unprime_elem (e:elem) : elem =  priming_elem false (None, false) e
let prime_cell (c:cell) : cell   =  priming_cell true    (None, true) c
let unprime_cell (c:cell) : cell =  priming_cell false (None, false) c
let prime_mem (m:mem) : mem      =  priming_mem  true    (None, true) m
let unprime_mem (m:mem) : mem    =  priming_mem  false (None, false) m
let prime_int (i:integer) : integer = priming_int true (None, true) i
let unprime_int (i:integer) : integer =  priming_int false (None, false) i
let prime_addrarr (aa:addrarr) : addrarr =  priming_addrarray true (None, true) aa
let unprime_int (aa:addrarr) : addrarr =  priming_addrarray false (None, false) aa
let prime_tidarr (tt:tidarr) : tidarr =  priming_tidarray true (None, true) tt
let unprime_tidarr (tt:tidarr) : tidarr =  priming_tidarray false (None, false) tt
let prime_term (t:term) : term =  priming_term true (None, true) t
let unprime_term (t:term) : term =  priming_term false (None, false) t
let prime_atom (a:atom) : atom =  priming_atom true (None, true) a
let unprime_atom (a:atom) : atom =  priming_atom false (None, false) a
let prime (phi:formula) : formula =  priming_formula true (None, true) phi
let unprime (phi:formula) : formula =  priming_formula false (None, false) phi
let prime_only (prime_set:V.VarSet.t) (pPC:bool) (phi:formula) : formula =
	priming_formula true (Some prime_set, pPC) phi
let unprime_only (prime_set:V.VarSet.t) (pPC:bool) (phi:formula) : formula =
	priming_formula false (Some prime_set, pPC) phi
let prime_term_only (prime_set:V.VarSet.t) (t:term) : term =
	priming_term true (Some prime_set, true) t
let unprime_term_only (prime_set:V.VarSet.t) (t:term) : term =
	priming_term false (Some prime_set, false) t
let prime_option_tid (th:V.shared_or_local) : V.shared_or_local =
	priming_option_tid true (None, true) th
let unprime_option_tid (th:V.shared_or_local) : V.shared_or_local =
	priming_option_tid false (None, false) th
let prime_tid (th:tid) : tid =  priming_tid true (None, true) th
let unprime_tid (th:tid) : tid = priming_tid false (None, false) th




(* PRINTING FUNCTIONS *)

let rec tid_to_str (th:tid) : string =
  match th with
    VarTh v              -> V.to_str v
  | NoTid               -> sprintf "#"
  | CellLockId(cell)     -> sprintf "%s.lockid" (cell_to_str cell)
  | CellLockIdAt(cell,l) -> sprintf "%s.lockid[%s]" (cell_to_str cell)
                                                    (integer_to_str l)
  | TidArrayRd(arr,t)   -> sprintf "%s[%s]" (arrays_to_str arr)
                                             (param_tid_to_str t)
  | TidArrRd(arr,l)     -> sprintf "%s[%s]" (tidarr_to_str arr)
                                             (integer_to_str l)


and param_tid_to_str (expr:tid) : string =
    match expr with
    VarTh v       -> begin
                       try
                         sprintf "[%i]" (int_of_string (V.id v))
                       with
                         _ -> sprintf "(%s)" (V.to_str v)
                     end
  | NoTid        -> sprintf "(#)"
  | CellLockId _  -> sprintf "(%s)" (tid_to_str expr)
  | CellLockIdAt _-> sprintf "(%s)" (tid_to_str expr)
  | TidArrayRd _ -> sprintf "(%s)" (tid_to_str expr)
  | TidArrRd _   -> sprintf "(%s)" (tid_to_str expr)


and tid_option_to_str (expr:tid option) : string =
  Option.map_default param_tid_to_str "" expr


and atom_to_str (expr:atom) : string =
  match expr with
    Append(p1,p2,pres)                -> sprintf "append(%s,%s,%s)"
                                                    (path_to_str p1)
                                                    (path_to_str p2)
                                                    (path_to_str pres)
  | Reach(h,add_from,add_to,p)        -> sprintf "reach(%s,%s,%s,%s)"
                                                    (mem_to_str h)
                                                    (addr_to_str add_from)
                                                    (addr_to_str add_to)
                                                    (path_to_str p)
  | ReachAt(h,a_from,a_to,l,p)        -> sprintf "reach(%s,%s,%s,%s,%s)"
                                                    (mem_to_str h)
                                                    (addr_to_str a_from)
                                                    (addr_to_str a_to)
                                                    (integer_to_str l)
                                                    (path_to_str p)
  | OrderList(h,a_from,a_to)          -> sprintf "orderlist(%s,%s,%s)"
                                                    (mem_to_str h)
                                                    (addr_to_str a_from)
                                                    (addr_to_str a_to)
  | Skiplist(h,s,l,a_from,a_to,elems) -> sprintf "skiplist(%s,%s,%s,%s,%s,%s)"
                                                  (mem_to_str h)
                                                  (set_to_str s)
                                                  (integer_to_str l)
                                                  (addr_to_str a_from)
                                                  (addr_to_str a_to)
                                                  (setelem_to_str elems)
  | In(a,s)                           -> sprintf "%s in %s "
                                                    (addr_to_str a) (set_to_str s)
  | SubsetEq(s_in,s_out)              -> sprintf "%s subseteq %s"
                                                    (set_to_str s_in)
                                                    (set_to_str s_out)
  | InTh(th,s)                        -> sprintf "%s inTh %s"
                                                    (tid_to_str th)
                                                    (setth_to_str s)
  | SubsetEqTh(s_in,s_out)            -> sprintf "%s subseteqTh %s"
                                                    (setth_to_str s_in)
                                                    (setth_to_str s_out)
  | InInt(i,s)                        -> sprintf "%s inInt %s"
                                                    (integer_to_str i)
                                                    (setint_to_str s)
  | SubsetEqInt(s_in,s_out)           -> sprintf "%s subseteqInt %s"
                                                    (setint_to_str s_in)
                                                    (setint_to_str s_out)
  | InElem(e,s)                       -> sprintf "%s inElem %s"
                                                    (elem_to_str e)
                                                    (setelem_to_str s)
  | SubsetEqElem(s_in,s_out)          -> sprintf "%s subseteqElem %s"
                                                    (setelem_to_str s_in)
                                                    (setelem_to_str s_out)
  | Less(i1,i2)                       -> sprintf "%s < %s"
                                                    (integer_to_str i1)
                                                    (integer_to_str i2)
  | Greater(i1,i2)                    -> sprintf "%s > %s"
                                                    (integer_to_str i1)
                                                    (integer_to_str i2)
  | LessEq(i1,i2)                     -> sprintf "%s <= %s"
                                                    (integer_to_str i1)
                                                    (integer_to_str i2)
  | GreaterEq(i1,i2)                  -> sprintf "%s >= %s"
                                                    (integer_to_str i1)
                                                    (integer_to_str i2)
  | LessTid(t1,t2)                    -> sprintf "%s < %s"
                                                    (tid_to_str t1)
                                                    (tid_to_str t2)
  | LessElem(e1,e2)                   -> sprintf "%s < %s"
                                                    (elem_to_str e1)
                                                    (elem_to_str e2)
  | GreaterElem(e1,e2)                -> sprintf "%s > %s"
                                                    (elem_to_str e1)
                                                    (elem_to_str e2)
  | Eq(exp)                           -> eq_to_str (exp)
  | InEq(exp)                         -> diseq_to_str (exp)
  | BoolVar v                         -> V.to_str v
  | BoolArrayRd(arr,t)                -> sprintf "%s%s" (arrays_to_str arr)
                                                         (param_tid_to_str t)
  | PC (pc,t,p)                       ->
          let t_str =
            match p with
              true -> V.shared_or_local_to_str (prime_option_tid t)
            | false -> V.shared_or_local_to_str t in
                                  let v_name =
            match p with
              true    -> V.prime_var_id Conf.pc_name
            | false -> Conf.pc_name
                                  in
                                    sprintf "%s%s=%i" v_name t_str pc
  | PCUpdate (pc,t)                   -> let t_str = tid_to_str t
                                         in
                                           sprintf"pc' = pc{%s<-%i}" t_str pc
  | PCRange (pc1,pc2,t,p)             ->
          let t_str =
            match p with true -> V.shared_or_local_to_str (prime_option_tid t)
            | false -> V.shared_or_local_to_str t in
                                  let v_name =
            match p with
              true    -> V.prime_var_id Conf.pc_name
            | false -> Conf.pc_name
                                  in
                                    sprintf "%s%s = [%i,%i]" v_name t_str pc1 pc2


and literal_to_str (expr:literal) : string =
  match expr with
  | Formula.Atom a    -> atom_to_str a
  | Formula.NegAtom a -> sprintf "~ %s" (atom_to_str a)


and arrays_to_str (expr:arrays) : string =
  match expr with
    VarArray v       -> V.to_str v
  | ArrayUp(arr,t,e) -> sprintf "arrUpd(%s,%s,%s)" (arrays_to_str arr)
                                                   (tid_to_str t)
                                                   (expr_to_str e)


and addrarr_to_str (expr:addrarr) : string =
  match expr with
    VarAddrArray v       -> V.to_str v
  | AddrArrayUp(arr,i,a) -> sprintf "addrArrUpd(%s,%s,%s)" (addrarr_to_str arr)
                                                           (integer_to_str i)
                                                           (addr_to_str a)
  | CellArr c            -> sprintf "%s.arr" (cell_to_str c)


and tidarr_to_str (expr:tidarr) : string =
  match expr with
    VarTidArray v       -> V.to_str v
  | TidArrayUp(arr,i,t) -> sprintf "tidArrUpd(%s,%s,%s)" (tidarr_to_str arr)
                                                         (integer_to_str i)
                                                         (tid_to_str t)
  | CellTids c            -> sprintf "%s.tids" (cell_to_str c)


and integer_to_str (expr:integer) : string =
  match expr with
    IntVal (i)        -> string_of_int i
  | VarInt v          -> V.to_str v
  | IntNeg i          -> sprintf "-%s" (integer_to_str i)
  | IntAdd (i1,i2)    -> sprintf "%s + %s" (integer_to_str i1)
                                           (integer_to_str i2)
  | IntSub (i1,i2)    -> sprintf "%s - %s" (integer_to_str i1)
                                           (integer_to_str i2)
  | IntMul (i1,i2)    -> sprintf "%s * %s" (integer_to_str i1)
                                           (integer_to_str i2)
  | IntDiv (i1,i2)    -> sprintf "%s / %s" (integer_to_str i1)
                                           (integer_to_str i2)
  | IntArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                        (param_tid_to_str t)
  | IntSetMin(s)      -> sprintf "setIntMin(%s)" (setint_to_str s)
  | IntSetMax(s)      -> sprintf "setIntMax(%s)" (setint_to_str s)
  | CellMax(c)        -> sprintf "%s.max" (cell_to_str c)
  | HavocLevel        -> sprintf "havocLevel()"


and mem_to_str (expr:mem) : string =
  match expr with
    VarMem v             -> V.to_str v
  | Update(mem,add,cell) -> sprintf "upd(%s,%s,%s)" (mem_to_str mem)
                                                    (addr_to_str add)
                                                    (cell_to_str cell)
  | MemArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str arr)
                                           (param_tid_to_str t)


and path_to_str (expr:path) : string =
  match expr with
    VarPath v                        -> V.to_str v
  | Epsilon                          -> sprintf "epsilon"
  | SimplePath(addr)                 -> sprintf "[ %s ]" (addr_to_str addr)
  | GetPath(mem,add_from,add_to)     -> sprintf "getp(%s,%s,%s)"
                                                  (mem_to_str mem)
                                                  (addr_to_str add_from)
                                                  (addr_to_str add_to)
  | GetPathAt(mem,add_from,add_to,l) -> sprintf "getp(%s,%s,%s,%s)"
                                                  (mem_to_str mem)
                                                  (addr_to_str add_from)
                                                  (addr_to_str add_to)
                                                  (integer_to_str l)
  | PathArrayRd(arr,t)               -> sprintf "%s%s" (arrays_to_str arr)
                                                       (param_tid_to_str t)


and set_to_str (expr:set) : string =
  match expr with
    VarSet v            -> V.to_str v
  | EmptySet            -> "EmptySet"
  | Singl(addr)         -> sprintf "{ %s }" (addr_to_str addr)
  | Union(s1,s2)        -> sprintf "Union(%s,%s)" (set_to_str s1)
                                                  (set_to_str s2)
  | Intr(s1,s2)         -> sprintf "Intr(%s,%s)" (set_to_str s1)
                                                 (set_to_str s2)
  | Setdiff(s1,s2)      -> sprintf "SetDiff(%s,%s)" (set_to_str s1)
                                                    (set_to_str s2)
  | PathToSet(path)     -> sprintf "path2set(%s)" (path_to_str path)
  | AddrToSet(mem,addr) -> sprintf "addr2set(%s,%s)" (mem_to_str mem)
                                                     (addr_to_str addr)
  | AddrToSetAt(mem,a,l)-> sprintf "addr2set(%s,%s,%s)" (mem_to_str mem)
                                                        (addr_to_str a)
                                                        (integer_to_str l)
  | SetArrayRd(arr,t)   -> sprintf "%s%s" (arrays_to_str arr)
                                          (param_tid_to_str t)


and setth_to_str (expr:setth) : string =
  match expr with
    VarSetTh v          -> V.to_str v
  | EmptySetTh          -> "EmptySetTh"
  | SinglTh(th)         -> sprintf "SinglTh(%s)" (tid_to_str th)
  | UnionTh(s_1,s_2)    -> sprintf "UnionTh(%s,%s)" (setth_to_str s_1)
                                                    (setth_to_str s_2)
  | IntrTh(s_1,s_2)     -> sprintf "IntrTh(%s,%s)" (setth_to_str s_1)
                                                   (setth_to_str s_2)
  | SetdiffTh(s_1,s_2)  -> sprintf "SetDiffTh(%s,%s)" (setth_to_str s_1)
                                                      (setth_to_str s_2)
  | SetThArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                          (param_tid_to_str t)


and setint_to_str (expr:setint) : string =
  match expr with
    VarSetInt v          -> V.to_str v
  | EmptySetInt          -> "EmptySetInt"
  | SinglInt(th)         -> sprintf "SinglInt(%s)" (integer_to_str th)
  | UnionInt(s_1,s_2)    -> sprintf "UnionInt(%s,%s)" (setint_to_str s_1)
                                                      (setint_to_str s_2)
  | IntrInt(s_1,s_2)     -> sprintf "IntrInt(%s,%s)" (setint_to_str s_1)
                                                     (setint_to_str s_2)
  | SetdiffInt(s_1,s_2)  -> sprintf "SetDiffInt(%s,%s)" (setint_to_str s_1)
                                                        (setint_to_str s_2)
  | SetIntArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                           (param_tid_to_str t)


and setelem_to_str (expr:setelem) : string =
  match expr with
    VarSetElem v          -> V.to_str v
  | EmptySetElem          -> "EmptySetElem"
  | SinglElem(e)          -> sprintf "SinglElem(%s)" (elem_to_str e)
  | UnionElem(s_1,s_2)    -> sprintf "UnionElem(%s,%s)" (setelem_to_str s_1)
                                                        (setelem_to_str s_2)
  | IntrElem(s_1,s_2)     -> sprintf "IntrElem(%s,%s)" (setelem_to_str s_1)
                                                       (setelem_to_str s_2)
  | SetdiffElem(s_1,s_2)  -> sprintf "SetDiffElem(%s,%s)" (setelem_to_str s_1)
                                                         (setelem_to_str s_2)
  | SetToElems(s,m)       -> sprintf "set2elem(%s,%s)" (set_to_str s)
                                                       (mem_to_str m)
  | SetElemArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                            (param_tid_to_str t)


and cell_to_str (expr:cell) : string =
  let list_str f xs = String.concat "," (List.map f xs) in
  match expr with
    VarCell v              -> V.to_str v
  | Error                  -> "error"
  | MkCell(data,addr,th)   -> sprintf "mkcell(%s,%s,%s)"
                                           (elem_to_str data)
                                           (addr_to_str addr)
                                           (tid_to_str th)
  | MkSLKCell(data,aa,tt)  -> sprintf "mkcell(%s,[%s],[%s])"
                                           (elem_to_str data)
                                           (list_str addr_to_str aa)
                                           (list_str tid_to_str tt)
  | MkSLCell(data,aa,ta,l) -> sprintf "mkcell(%s,%s,%s,%s)"
                                           (elem_to_str data)
                                           (addrarr_to_str aa)
                                           (tidarr_to_str ta)
                                           (integer_to_str l)
  | CellLock(cell,t)        -> sprintf "%s.lock[%s]" (cell_to_str cell)
                                                     (tid_to_str t)
  | CellLockAt(cell,l,t)    -> sprintf "%s.lock[%s,%s]" (cell_to_str cell)
                                                        (integer_to_str l)
                                                        (tid_to_str t)
  | CellUnlock(cell)      -> sprintf "%s.unlock" (cell_to_str cell)
  | CellUnlockAt(cell,l)  -> sprintf "%s.unlockat(%s)" (cell_to_str cell)
                                                     (integer_to_str l)
  | CellAt(mem,addr)      -> sprintf "rd(%s,%s)" (mem_to_str mem)
                                                 (addr_to_str addr)
  | CellArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str arr)
                                            (param_tid_to_str t)
  | UpdCellAddr(c,i,a)    -> sprintf "updCellAddr(%s,%s,%s)" (cell_to_str c)
                                                             (integer_to_str i)
                                                             (addr_to_str a)


and addr_to_str (expr:addr) :string =
  match expr with
    VarAddr v                 -> V.to_str v
  | Null                      -> "null"
  | Next(cell)                -> sprintf "%s.next" (cell_to_str cell)
  | NextAt(cell,l)            -> sprintf "%s.nextat[%s]" (cell_to_str cell)
                                                         (integer_to_str l)
  | ArrAt(cell,l)             -> sprintf "%s.arr[%s]" (cell_to_str cell)
                                                      (integer_to_str l)
  | FirstLocked(mem,path)     -> sprintf "firstlocked(%s,%s)"
                                            (mem_to_str mem)
                                            (path_to_str path)
  | FirstLockedAt(mem,path,l) -> sprintf "firstlocked(%s,%s,%s)"
                                            (mem_to_str mem)
                                            (path_to_str path)
                                            (integer_to_str l)
  | AddrArrayRd(arr,t)        -> sprintf "%s[%s]" (arrays_to_str arr)
                                                  (param_tid_to_str t)
  | AddrArrRd(arr,l)          -> sprintf "%s[%s]" (addrarr_to_str arr)
                                                  (integer_to_str l)


and eq_to_str ((e1,e2):eq) : string =
      sprintf "%s = %s" (term_to_str e1) (term_to_str e2)


and diseq_to_str (expr:diseq) : string =
    let (e1,e2) = expr in
      sprintf "%s != %s" (term_to_str e1) (term_to_str e2)


and elem_to_str (expr:elem) : string =
  match expr with
    VarElem v          -> V.to_str v
  | CellData(cell)     -> sprintf "%s.data" (cell_to_str cell)
  | ElemArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                         (param_tid_to_str t)
  | HavocListElem      -> "havocListElem()"
  | HavocSkiplistElem  -> "havocSLElem()"
  | LowestElem         -> "lowestElem"
  | HighestElem        -> "highestElem"


and term_to_str (expr:term) : string =
  match expr with
    VarT v            -> V.to_str v
  | SetT(set)         -> (set_to_str set)
  | AddrT(addr)       -> (addr_to_str addr)
  | ElemT(elem)       -> (elem_to_str elem)
  | TidT(th)         -> (tid_to_str th)
  | CellT(cell)       -> (cell_to_str cell)
  | SetThT(setth)     -> (setth_to_str setth)
  | SetIntT(setint)   -> (setint_to_str setint)
  | SetElemT(setelem) -> (setelem_to_str setelem)
  | PathT(path)       -> (path_to_str path)
  | MemT(mem)         -> (mem_to_str mem)
  | IntT(i)           -> (integer_to_str i)
  | ArrayT(arr)       -> (arrays_to_str arr)
  | AddrArrayT(arr)   -> (addrarr_to_str arr)
  | TidArrayT(arr)    -> (tidarr_to_str arr)


and expr_to_str (expr:expr_t) : string =
  match expr with
    Term t    -> term_to_str t
  | Formula b -> formula_to_str b


and conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  Formula.conjunctive_formula_to_str atom_to_str cf

and formula_to_str (phi:formula) : string =
  Formula.formula_to_str atom_to_str phi

(*
and conjunctive_formula_to_str (expr:conjunctive_formula) : string =
  match expr with
  | Formula.FalseConj -> "false"
  | Formula.TrueConj  -> "true"
  | Formula.Conj ls   -> String.concat " /\\ " $ List.map literal_to_str ls


and formula_to_str_aux (op:logic_op_t) (phi:formula) : string =
  match phi with
  | Formula.Literal l -> literal_to_str l
  | Formula.True -> "true"
  | Formula.False -> "false"
  | And(a,b)     -> let a_str = formula_to_str_aux AndOp a in
                    let b_str = formula_to_str_aux AndOp b in
                    if op = AndOp then
                      a_str ^ " /\\ " ^ b_str
                    else
                      "(" ^ a_str ^ " /\\ " ^ b_str ^ ")"
  | Or(a,b)      -> let a_str = formula_to_str_aux OrOp a in
                    let b_str = formula_to_str_aux OrOp b in
                    if op = OrOp then
                      a_str ^ " \\/ " ^ b_str
                    else
                      "(" ^ a_str ^ " \\/ " ^ b_str ^ ")"
  | Not a        -> let a_str = formula_to_str_aux NotOp a in
                    if op = NotOp then
                      "~ " ^ a_str
                    else
                      "(~ " ^ a_str ^ ")"
  | Implies(a,b) -> let a_str = formula_to_str_aux ImpliesOp a in
                    let b_str = formula_to_str_aux ImpliesOp b in
                    if op = ImpliesOp then
                      a_str ^ " -> " ^ b_str
                    else
                      "(" ^ a_str ^ " -> " ^ b_str ^ ")"
  | Iff(a,b)     -> let a_str = formula_to_str_aux IffOp a in
                    let b_str = formula_to_str_aux IffOp b in
                    if op = IffOp then
                      a_str ^ " <-> " ^ b_str
                    else
                      "(" ^ a_str ^ " <-> " ^ b_str ^ ")"


and formula_to_str (expr:formula) : string =
  formula_to_str_aux NoneOp expr
*)

let var_to_term (v:V.t) : term =
  match V.sort v with
    Unknown   -> VarT       v
  | Set       -> SetT       (VarSet        v)
  | Elem      -> ElemT      (VarElem       v)
  | Tid       -> TidT       (VarTh         v)
  | Addr      -> AddrT      (VarAddr       v)
  | Cell      -> CellT      (VarCell       v)
  | SetTh     -> SetThT     (VarSetTh      v)
  | SetInt    -> SetIntT    (VarSetInt     v)
  | SetElem   -> SetElemT   (VarSetElem    v)
  | Path      -> PathT      (VarPath       v)
  | Mem       -> MemT       (VarMem        v)
  | Int       -> IntT       (VarInt        v)
  | Array     -> ArrayT     (VarArray      v)
  | AddrArray -> AddrArrayT (VarAddrArray  v)
  | TidArray  -> TidArrayT  (VarTidArray   v)
  | Bool      -> VarT    v


let term_to_var (t:term) : V.t =
  match t with
    VarT v -> v
  | SetT  (VarSet v)   -> V.set_sort v Set
  | ElemT (VarElem v)  -> V.set_sort v Elem
  | TidT  (VarTh v)    -> V.set_sort v Tid
  | AddrT (VarAddr v)  -> V.set_sort v Addr
  | CellT (VarCell v)  -> V.set_sort v Cell
  | SetThT(VarSetTh v) -> V.set_sort v SetTh
  | PathT (VarPath v)  -> V.set_sort v Path
  | MemT  (VarMem v)   -> V.set_sort v Mem
  | IntT  (VarInt v)   -> V.set_sort v Int
  | ArrayT(VarArray v) -> V.set_sort v Array
  | _                  -> raise(No_variable_term(term_to_str t))



let term_sort (t:term) : sort =
  match t with
    VarT v       -> V.sort v
  | SetT _       -> Set
  | ElemT _      -> Elem
  | TidT _       -> Tid
  | AddrT _      -> Addr
  | CellT _      -> Cell
  | SetThT _     -> SetTh
  | SetIntT _    -> SetInt
  | SetElemT _   -> SetElem
  | PathT _      -> Path
  | MemT _       -> Mem
  | IntT _       -> Int
  | ArrayT _     -> Array
  | AddrArrayT _ -> AddrArray
  | TidArrayT _  -> TidArray


(* Vocabulary to variable conversion *)
let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)


let voc_to_vars (ts:ThreadSet.t) : V.VarSet.t =
  ThreadSet.fold (fun t set ->
    V.VarSet.add (voc_to_var t) set
  ) ts V.VarSet.empty
(*
  List.map voc_to_var ts
*)


(* Equality constructor functions for formulas *)
let eq_set (s1:set) (s2:set) : formula =
  Formula.atom_to_formula (Eq (SetT s1, SetT s2))

let eq_elem (e1:elem) (e2:elem) : formula =
  Formula.atom_to_formula (Eq (ElemT e1, ElemT e2))

let eq_tid (t1:tid) (t2:tid) : formula =
  Formula.atom_to_formula (Eq (TidT t1, TidT t2))

let eq_addr (a1:addr) (a2:addr) : formula =
  Formula.atom_to_formula (Eq (AddrT a1, AddrT a2))

let eq_cell (c1:cell) (c2:cell) : formula =
  Formula.atom_to_formula (Eq (CellT c1, CellT c2))

let eq_setth (s1:setth) (s2:setth) : formula =
  Formula.atom_to_formula (Eq (SetThT s1, SetThT s2))

let eq_setint (s1:setint) (s2:setint) : formula =
  Formula.atom_to_formula (Eq (SetIntT s1, SetIntT s2))

let eq_setelem (s1:setelem) (s2:setelem) : formula =
  Formula.atom_to_formula (Eq (SetElemT s1, SetElemT s2))

let eq_path (p1:path) (p2:path) : formula =
  Formula.atom_to_formula (Eq (PathT p1, PathT p2))

let eq_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Eq (IntT i1, IntT i2))

let eq_mem (m1:mem) (m2:mem) : formula =
  Formula.atom_to_formula (Eq (MemT m1, MemT m2))

let eq_array (a1:arrays) (a2:arrays) : formula =
  Formula.atom_to_formula (Eq (ArrayT a1, ArrayT a2))

let eq_addrarr (a1:addrarr) (a2:addrarr) : formula =
  Formula.atom_to_formula (Eq (AddrArrayT a1, AddrArrayT a2))

let eq_tidarr (a1:tidarr) (a2:tidarr) : formula =
  Formula.atom_to_formula (Eq (TidArrayT a1, TidArrayT a2))

let eq_term (t1:term) (t2:term) : formula =
  Formula.atom_to_formula (Eq (t1, t2))

let eq_tid (t1:tid) (t2:tid) : formula =
  Formula.atom_to_formula (Eq (TidT t1, TidT t2))

let ineq_addr (a1:addr) (a2:addr) : formula =
  Formula.atom_to_formula (InEq (AddrT a1, AddrT a2))

let ineq_elem (e1:elem) (e2:elem) : formula =
  Formula.atom_to_formula (InEq (ElemT e1, ElemT e2))

let ineq_tid (t1:tid) (t2:tid) : formula =
  Formula.atom_to_formula (InEq (TidT t1, TidT t2))

let atom_form (a:atom) : formula =
  Formula.atom_to_formula a

let pc_form (pc:pc_t) (th:V.shared_or_local) (pr:bool) : formula =
  Formula.atom_to_formula (PC (pc,th,pr))

let pcrange_form (pc1:pc_t) (pc2:pc_t) (th:V.shared_or_local) (pr:bool) : formula =
  Formula.atom_to_formula (PCRange (pc1,pc2,th,pr))

let pcupd_form (pc:pc_t) (th:tid) : formula =
  Formula.atom_to_formula (PCUpdate (pc,th))

let less_form (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Less (i1, i2))

let lesseq_form (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (LessEq (i1, i2))

let greater_form (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Greater (i1, i2))

let greatereq_form (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (GreaterEq (i1, i2))

let subset_form (s1:set) (s2:set) : formula =
  Formula.atom_to_formula (SubsetEq (s1, s2))

let subsetth_form (s1:setth) (s2:setth) : formula =
  Formula.atom_to_formula (SubsetEqTh (s1, s2))

let subsetint_form (s1:setint) (s2:setint) : formula =
  Formula.atom_to_formula (SubsetEqInt (s1, s2))

let in_form (a:addr) (s:set) : formula =
  Formula.atom_to_formula (In (a, s))

let inth_form (t:tid) (s:setth) : formula =
  Formula.atom_to_formula (InTh (t, s))

let inint_form (i:integer) (s:setint) : formula =
  Formula.atom_to_formula (InInt (i, s))

let boolvar (v:V.t) : formula =
  Formula.atom_to_formula (BoolVar v)


(* Operation constructor functions *)
let exp_in (a:addr) (s:set) : formula =
  Formula.atom_to_formula (In (a,s))

let exp_subset (s1:set) (s2:set) : formula =
  Formula.atom_to_formula (SubsetEq (s1,s2))

let exp_inth (t:tid) (s:setth) : formula =
  Formula.atom_to_formula (InTh (t,s))

let exp_subsetth (s1:setth) (s2:setth) : formula =
  Formula.atom_to_formula (SubsetEqTh (s1,s2))

let exp_inint (i:integer) (s:setint) : formula =
  Formula.atom_to_formula (InInt (i,s))

let exp_subsetint (s1:setint) (s2:setint) : formula =
  Formula.atom_to_formula (SubsetEqInt (s1,s2))

let exp_less (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Less (i1,i2))

let exp_greater (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Greater (i1,i2))

let exp_lesseq (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (LessEq (i1,i2))

let exp_greatereq (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (GreaterEq (i1,i2))



(* TERMSET MANIPULATION FUNCTIONS *)

let construct_term_set (xs:term list) : TermSet.t =
  List.fold_left (fun s t -> TermSet.add t s) (TermSet.empty) xs


let filter_term_set (t_list:term list) (t_set:TermSet.t) : TermSet.t =
  let aux s t = match t with
                  AddrT(Next(VarCell var as c)) ->
                    if TermSet.mem t s then
                      TermSet.remove t s
                    else if TermSet.mem (CellT c) s then
                      begin
                        let set'=TermSet.remove(CellT c) s in
                        let new_terms=[TidT(CellLockId c); ElemT(CellData c)] 
                        in
                        let new_elems = construct_term_set new_terms in
                          TermSet.union set' new_elems
                      end
                    else
                      s
                | TidT(CellLockId c) ->
                    if TermSet.mem t s then
                      TermSet.remove t s
                    else if TermSet.mem (CellT c) s then
                      begin
                        let set'=TermSet.remove(CellT c) s in
                        let new_terms=[AddrT(Next c); ElemT(CellData c)] in
                        let new_elems = construct_term_set new_terms in
                          TermSet.union set' new_elems
                      end
                    else
                      s
                | ElemT(CellData c) ->
                    if TermSet.mem t s then
                      TermSet.remove t s
                    else if TermSet.mem (CellT c) s then
                      begin
                        let set'=TermSet.remove(CellT c) s in
                        let new_terms =
                              [AddrT(Next c); TidT(CellLockId c)] in
                        let new_elems = construct_term_set new_terms in
                          TermSet.union set' new_elems
                      end
                    else
                      s
                | _ -> TermSet.remove t s
  in
    List.fold_left aux t_set t_list



(* THREAD IDENTIFIER INFORMATION FUNCTIONS *)
let is_tid_var (t:tid) : bool =
  match t with
    VarTh v -> begin
                 try
                   let _ = int_of_string (V.id v) in false
                 with
                   _ -> true
               end
  | _       -> false


let is_tid_val (t:tid) : bool =
  match t with
    VarTh v -> begin
                 try
                   let _ = int_of_string (V.id v) in true
                 with
                   _ -> false
               end
  | _       -> false


let is_tid_nolock (t:tid) : bool =
  match t with
    NoTid -> true
  | _      -> false


let is_tid_lockid (t:tid) : bool =
  match t with
    CellLockId _ -> true
  | _            -> false

(* TERM INFORMATION *)

let term_info (t:term)
      : V.id * bool * V.shared_or_local * V.procedure_name * var_nature =
  let get_info v = (V.id v,
                    V.is_primed v,
                    V.parameter v,
                    V.scope v,
                    (V.info v).nature)
  in
  match t with
  | VarT v                           -> get_info v
  | SetT(VarSet v)                   -> get_info v
  | ElemT(VarElem v)                 -> get_info v
  | TidT(VarTh v)                    -> get_info v
  | AddrT(VarAddr v)                 -> get_info v
  | CellT(VarCell v)                 -> get_info v
  | SetThT(VarSetTh v)               -> get_info v
  | PathT(VarPath v)                 -> get_info v
  | MemT(VarMem v)                   -> get_info v
  | IntT(VarInt v)                   -> get_info v
  | ElemT(CellData(VarCell v))       -> get_info v
  | AddrT(Next(VarCell v))           -> get_info v
  | TidT(CellLockId(VarCell v))      -> get_info v
  | CellT(CellLock(VarCell v,_))     -> get_info v
  | CellT(CellUnlock(VarCell v))     -> get_info v
  | CellT(CellLockAt(VarCell v,_,_)) -> get_info v
  | CellT(CellUnlockAt(VarCell v,_)) -> get_info v
  | _                                -> ("",false,V.Shared,V.GlobalScope,RealVar)


let term_id (t:term) : V.id =
  let (v,_,_,_,_) = term_info t in v


let term_primed (t:term) : bool =
  let (_,pr,_,_,_) = term_info t in pr


let term_parameter (t:term) : V.shared_or_local =
  let (_,_,th,_,_) = term_info t in th


let term_scope (t:term) : V.procedure_name =
  let (_,_,_,p,_) = term_info t in p


let term_nature (t:term) : var_nature =
  let (_,_,_,_,k) = term_info t in k


(* THREAD LIST GENERATION FUNCTIONS *)



let rec gen_tid_list (min:int) (max:int) : tid list =
  if min > max then
    []
  else
    (VarTh (build_num_tid_var min)) :: gen_tid_list (min+1) max


let rec gen_tid_list_except (min:int) (max:int) (t:tid) : tid list =
  if min > max then
    []
  else
    let new_th = VarTh (build_num_tid_var min) in
    if new_th <> t then
      new_th :: gen_tid_list_except (min+1) max t
    else
      gen_tid_list_except (min+1) max t


let gen_fresh_tid (set:ThreadSet.t) : tid =
  let rec find n =
    let th_cand_id = sprintf "k_%i" n in
    let th_cand = VarTh (build_global_var th_cand_id Tid)in
      if ThreadSet.mem th_cand set then find (n+1) else th_cand
  in
    find 0


let rec gen_fresh_tid_set (set:ThreadSet.t) (n:int) : ThreadSet.t =
  match n with
    0 -> ThreadSet.empty
  | m -> let new_th = gen_fresh_tid set in
           ThreadSet.add new_th (gen_fresh_tid_set (ThreadSet.add new_th set) (m-1))


(* PRINTING FUNCTIONS *)

let pc_to_str (p:pc_t) : string =
  string_of_int p


let sort_to_str (s:sort) : string =
  match s with
      Set       -> "addrSet"
    | Elem      -> "elem"
    | Tid      -> "tid"
    | Addr      -> "addr"
    | Cell      -> "cell"
    | SetTh     -> "tidSet"
    | SetInt    -> "intSet"
    | SetElem   -> "elemSet"
    | Path      -> "path"
    | Mem       -> "mem"
    | Bool      -> "bool"
    | Int       -> "int"
    | Array     -> "array"
    | AddrArray -> "addrarr"
    | TidArray  -> "tidarr"
    | Unknown   -> "unknown"

 

(* Expression conversion functions *)
let get_initVal_restriction (v:initVal_t) : expr_t =
  match v with
    Equality t  -> Term t
  | Condition c ->
      begin
        match c with
        | F.Literal (F.Atom (In          (_,s))) -> Term (SetT s)
        | F.Literal (F.Atom (SubsetEq    (_,s))) -> Term (SetT s)
        | F.Literal (F.Atom (InTh        (_,s))) -> Term (SetThT s)
        | F.Literal (F.Atom (SubsetEqTh  (_,s))) -> Term (SetThT s)
        | F.Literal (F.Atom (InInt       (_,s))) -> Term (SetIntT s)
        | F.Literal (F.Atom (SubsetEqInt (_,s))) -> Term (SetIntT s)
        | F.Literal (F.Atom (Less        (_,i))) -> Term (IntT i)
        | F.Literal (F.Atom (Greater     (_,i))) -> Term (IntT i)
        | F.Literal (F.Atom (LessEq      (_,i))) -> Term (IntT i)
        | F.Literal (F.Atom (GreaterEq   (_,i))) -> Term (IntT i)
        | _                                  -> Formula c
(*
        | _ -> Interface.Err.msg "Invalid argument" $
                sprintf "Function get_initVal_restrictions was expecting a \
                         condition over integers or sets. Instead, \"%s\" was \
                         received." (formula_to_str c);
               raise(Invalid_argument)
*)
      end


let term_to_integer (t:term) : integer =
  match t with
    IntT i -> i
  | _      -> Interface.Err.msg "Not an integer term" $
                sprintf "Impossible to convert to integer a non integer \
                         term. An integer term was expected, but \"%s\" was \
                         received." (term_to_str t);
              raise(Invalid_argument)


let term_to_set (t:term) : set =
  match t with
    SetT s -> s
  | _      -> Interface.Err.msg "Not a set term" $
                sprintf "Impossible to convert to set a non set \
                         term. A set term was expected, but \"%s\" was \
                         received." (term_to_str t);
              raise(Invalid_argument)


let term_to_setth (t:term) : setth =
  match t with
    SetThT s -> s
  | _        -> Interface.Err.msg "Not a set of thread identifiers term" $
                  sprintf "Impossible to convert to set of thread identifiers \
                           a non set of thread identifiers term. A set of \
                           thread identifiers term was expected, but \"%s\" \
                           was received." (term_to_str t);
                raise(Invalid_argument)


let term_to_setint (t:term) : setint =
  match t with
    SetIntT s -> s
  | _        -> Interface.Err.msg "Not a set of integers term" $
                  sprintf "Impossible to convert to set of integers \
                           a non set of integers term. A set of \
                            integers term was expected, but \"%s\" \
                           was received." (term_to_str t);
                raise(Invalid_argument)



(* PRIMING QUERY FUNCTIONS *)

let (@@) = V.VarSet.union


let rec get_vars_term (expr:term) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match expr with
  | VarT v            -> V.VarSet.union (base v)
                          (match V.parameter v with
                           | V.Shared -> V.VarSet.empty
                           | V.Local t -> base t)
  | SetT(set)         -> get_vars_set set base
  | AddrT(addr)       -> get_vars_addr addr base
  | ElemT(elem)       -> get_vars_elem elem base
  | TidT(th)          -> get_vars_tid th base
  | CellT(cell)       -> get_vars_cell cell base
  | SetThT(setth)     -> get_vars_setth setth base
  | SetIntT(setint)   -> get_vars_setint setint base
  | SetElemT(setelem) -> get_vars_setelem setelem base
  | PathT(path)       -> get_vars_path path base
  | MemT(mem)         -> get_vars_mem mem base
  | IntT(i)           -> get_vars_int i base
  | ArrayT(arr)       -> get_vars_array arr base
  | AddrArrayT(arr)   -> get_vars_addrarr arr base
  | TidArrayT(arr)    -> get_vars_tidarr arr base


and get_vars_expr (e:expr_t) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match e with
    Term t    -> get_vars_term t base
  | Formula b -> get_vars_formula b base


and get_vars_array (a:arrays) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match a with
  | VarArray v       -> V.VarSet.union (base v)
                          (match V.parameter v with
                           | V.Shared -> V.VarSet.empty
                           | V.Local t -> base t)
  | ArrayUp(arr,t,e) -> (get_vars_array arr base) @@
                        (get_vars_tid t base)     @@
                        (get_vars_expr e base)


and get_vars_addrarr (a:addrarr) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match a with
    VarAddrArray v       -> V.VarSet.union (base v)
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | AddrArrayUp(arr,i,a) -> (get_vars_addrarr arr base) @@
                            (get_vars_int i base)       @@
                            (get_vars_addr a base)
  | CellArr c            -> (get_vars_cell c base)


and get_vars_tidarr (a:tidarr) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match a with
    VarTidArray v       -> V.VarSet.union (base v)
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | TidArrayUp(arr,i,t) -> (get_vars_tidarr arr base) @@
                           (get_vars_int i base)      @@
                           (get_vars_tid t base)
  | CellTids c            -> (get_vars_cell c base)


and get_vars_set (e:set) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match e with
    VarSet v            -> V.VarSet.union (base v)
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | EmptySet            -> V.VarSet.empty
  | Singl(addr)         -> (get_vars_addr addr base)
  | Union(s1,s2)        -> (get_vars_set s1 base) @@ (get_vars_set s2 base)
  | Intr(s1,s2)         -> (get_vars_set s1 base) @@ (get_vars_set s2 base)
  | Setdiff(s1,s2)      -> (get_vars_set s1 base) @@ (get_vars_set s2 base)
  | PathToSet(path)     -> (get_vars_path path base)
  | AddrToSet(mem,addr) -> (get_vars_mem mem base) @@ (get_vars_addr addr base)
  | AddrToSetAt(mem,a,l)-> (get_vars_mem mem base) @@
                           (get_vars_addr a base)  @@
                           (get_vars_int l base)
  | SetArrayRd(arr,t)   -> (get_vars_array arr base)


and get_vars_addr (a:addr) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match a with
    VarAddr v                 -> V.VarSet.union (base v)
                                  (match V.parameter v with
                                   | V.Shared -> V.VarSet.empty
                                   | V.Local t -> base t)
  | Null                      -> V.VarSet.empty
  | Next(cell)                -> (get_vars_cell cell base)
  | NextAt(cell,l)            -> (get_vars_cell cell base) @@ (get_vars_int l base)
  | ArrAt(cell,l)             -> (get_vars_cell cell base) @@ (get_vars_int l base)
  | FirstLocked(mem,path)     -> (get_vars_mem mem base) @@ (get_vars_path path base)
  | FirstLockedAt(mem,path,l) -> (get_vars_mem mem base) @@ (get_vars_path path base) @@
                                 (get_vars_int l base)
  | AddrArrayRd(arr,t)        -> (get_vars_array arr base)
  | AddrArrRd(arr,i)          -> (get_vars_addrarr arr base) @@ (get_vars_int i base)


and get_vars_elem (e:elem) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match e with
    VarElem v          -> V.VarSet.union (base v)
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | CellData(cell)     -> (get_vars_cell cell base)
  | ElemArrayRd(arr,t) -> (get_vars_array arr base)
  | HavocListElem      -> V.VarSet.empty
  | HavocSkiplistElem  -> V.VarSet.empty
  | LowestElem         -> V.VarSet.empty
  | HighestElem        -> V.VarSet.empty


and get_vars_tid (th:tid) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match th with
    VarTh v              -> V.VarSet.union (base v)
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | NoTid               -> V.VarSet.empty
  | CellLockId(cell)     -> (get_vars_cell cell base)
  | CellLockIdAt(cell,l) -> (get_vars_cell cell base) @@ (get_vars_int l base)
  | TidArrayRd(arr,t)   -> (get_vars_array arr base)
  | TidArrRd(arr,l)     -> (get_vars_tidarr arr base) @@ (get_vars_int l base)


and get_vars_cell (c:cell) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  let fold f xs = List.fold_left (fun ys x -> (f x base) @@ ys) V.VarSet.empty xs in
  match c with
    VarCell v              -> V.VarSet.union (base v)
                                (match V.parameter v with
                                 | V.Shared -> V.VarSet.empty
                                 | V.Local t -> base t)
  | Error                  -> V.VarSet.empty
  | MkCell(data,addr,th)   -> (get_vars_elem data base) @@
                              (get_vars_addr addr base) @@
                              (get_vars_tid th base)
  | MkSLKCell(data,aa,tt)  -> (get_vars_elem data base) @@
                              (fold get_vars_addr aa)   @@
                              (fold get_vars_tid tt)
  | MkSLCell(data,aa,ta,l) -> (get_vars_elem data base) @@
                              (get_vars_addrarr aa base) @@
                              (get_vars_tidarr ta base) @@
                              (get_vars_int l base)
  | CellLock(cell,t)       -> (get_vars_cell cell base) @@ (get_vars_tid t base)
  | CellLockAt(cell,l,t)   -> (get_vars_cell cell base) @@
                              (get_vars_int l base)     @@
                              (get_vars_tid t base)
  | CellUnlock(cell)       -> (get_vars_cell cell base)
  | CellUnlockAt(cell,l)   -> (get_vars_cell cell base) @@
                              (get_vars_int l base)
  | CellAt(mem,addr)       -> (get_vars_mem mem base) @@
                              (get_vars_addr addr base)
  | CellArrayRd(arr,t)     -> (get_vars_array arr base)
  | UpdCellAddr(c,i,a)     -> (get_vars_cell c base) @@
                              (get_vars_int i base)  @@
                              (get_vars_addr a base)


and get_vars_setth (s:setth) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match s with
    VarSetTh v          -> (base v) @@
                            (match V.parameter v with
                             | V.Shared -> V.VarSet.empty
                             | V.Local t -> base t)
  | EmptySetTh          -> V.VarSet.empty
  | SinglTh(th)         -> get_vars_tid th base
  | UnionTh(s1,s2)      -> (get_vars_setth s1 base)@@(get_vars_setth s2 base)
  | IntrTh(s1,s2)       -> (get_vars_setth s1 base)@@(get_vars_setth s2 base)
  | SetdiffTh(s1,s2)    -> (get_vars_setth s1 base)@@(get_vars_setth s2 base)
  | SetThArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_setint (s:setint) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match s with
    VarSetInt v          -> (base v) @@
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | EmptySetInt          -> V.VarSet.empty
  | SinglInt(i)          -> (get_vars_int i base)
  | UnionInt(s1,s2)      -> (get_vars_setint s1 base) @@
                            (get_vars_setint s2 base)
  | IntrInt(s1,s2)       -> (get_vars_setint s1 base) @@
                            (get_vars_setint s2 base)
  | SetdiffInt(s1,s2)    -> (get_vars_setint s1 base) @@
                            (get_vars_setint s2 base)
  | SetIntArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_setelem (s:setelem) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match s with
    VarSetElem v          -> (base v) @@
                              (match V.parameter v with
                               | V.Shared -> V.VarSet.empty
                               | V.Local t -> base t)
  | EmptySetElem          -> V.VarSet.empty
  | SinglElem(e)          -> (get_vars_elem e base)
  | UnionElem(s1,s2)      -> (get_vars_setelem s1 base) @@
                             (get_vars_setelem s2 base)
  | IntrElem(s1,s2)       -> (get_vars_setelem s1 base) @@
                             (get_vars_setelem s2 base)
  | SetdiffElem(s1,s2)    -> (get_vars_setelem s1 base) @@
                             (get_vars_setelem s2 base)
  | SetToElems(s,m)       -> (get_vars_set s base) @@ (get_vars_mem m base)
  | SetElemArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_path (p:path) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match p with
    VarPath v -> (base v) @@
                    (match V.parameter v with
                     | V.Shared -> V.VarSet.empty
                     | V.Local t -> base t)
  | Epsilon                          -> V.VarSet.empty
  | SimplePath(addr)                 -> (get_vars_addr addr base)
  | GetPath(mem,add_from,add_to)     -> (get_vars_mem mem base) @@
                                        (get_vars_addr add_from base) @@
                                        (get_vars_addr add_to base)
  | GetPathAt(mem,add_from,add_to,l) -> (get_vars_mem mem base) @@
                                        (get_vars_addr add_from base) @@
                                        (get_vars_addr add_to base) @@
                                        (get_vars_int l base)
  | PathArrayRd(arr,t)               -> (get_vars_array arr base)


and get_vars_mem (m:mem) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match m with
    VarMem v             -> (base v) @@
                                (match V.parameter v with
                                 | V.Shared -> V.VarSet.empty
                                 | V.Local t -> base t)
  | Update(mem,add,cell) -> (get_vars_mem mem base) @@
                            (get_vars_addr add base) @@
                            (get_vars_cell cell base)
  | MemArrayRd(arr,t)    -> (get_vars_array arr base)


and get_vars_int (i:integer) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match i with
    IntVal(i)         -> V.VarSet.empty
  | VarInt v          -> (base v) @@
                            (match V.parameter v with
                             | V.Shared -> V.VarSet.empty
                             | V.Local t -> base t)
  | IntNeg(i)         -> (get_vars_int i base)
  | IntAdd(i1,i2)     -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | IntSub(i1,i2)     -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | IntMul(i1,i2)     -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | IntDiv(i1,i2)     -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | IntArrayRd(arr,t) -> (get_vars_array arr base)
  | IntSetMin(s)      -> (get_vars_setint s base)
  | IntSetMax(s)      -> (get_vars_setint s base)
  | CellMax(c)        -> (get_vars_cell c base)
  | HavocLevel        -> V.VarSet.empty


and get_vars_atom (a:atom) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match a with
    Append(p1,p2,pres)                 -> (get_vars_path p1 base) @@
                                          (get_vars_path p2 base) @@
                                          (get_vars_path pres base)
  | Reach(h,add_from,add_to,p)         -> (get_vars_mem h base) @@
                                          (get_vars_addr add_from base) @@
                                          (get_vars_addr add_to base) @@
                                          (get_vars_path p base)
  | ReachAt(h,a_from,a_to,l,p)         -> (get_vars_mem h base) @@
                                          (get_vars_addr a_from base) @@
                                          (get_vars_addr a_to base) @@
                                          (get_vars_int l base) @@
                                          (get_vars_path p base)
  | OrderList(h,a_from,a_to)           -> (get_vars_mem h base) @@
                                          (get_vars_addr a_from base) @@
                                          (get_vars_addr a_to base)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> (get_vars_mem h base) @@
                                          (get_vars_set s base) @@
                                          (get_vars_int l base) @@
                                          (get_vars_addr a_from base) @@
                                          (get_vars_addr a_to base) @@
                                          (get_vars_setelem elems base)
  | In(a,s)                            -> (get_vars_addr a base) @@ (get_vars_set s base)
  | SubsetEq(s_in,s_out)               -> (get_vars_set s_in base) @@
                                          (get_vars_set s_out base)
  | InTh(th,s)                         -> (get_vars_tid th base)@@(get_vars_setth s base)
  | SubsetEqTh(s_in,s_out)             -> (get_vars_setth s_in base) @@
                                          (get_vars_setth s_out base)
  | InInt(i,s)                         -> (get_vars_int i base) @@
                                          (get_vars_setint s base)
  | SubsetEqInt(s_in,s_out)            -> (get_vars_setint s_in base) @@
                                          (get_vars_setint s_out base)
  | InElem(e,s)                        -> (get_vars_elem e base) @@
                                          (get_vars_setelem s base)
  | SubsetEqElem(s_in,s_out)           -> (get_vars_setelem s_in base) @@
                                          (get_vars_setelem s_out base)
  | Less(i1,i2)                        -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | Greater(i1,i2)                     -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | LessEq(i1,i2)                      -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | GreaterEq(i1,i2)                   -> (get_vars_int i1 base) @@ (get_vars_int i2 base)
  | LessTid(t1,t2)                     -> (get_vars_tid t1 base) @@ (get_vars_tid t2 base)
  | LessElem(e1,e2)                    -> (get_vars_elem e1 base) @@ (get_vars_elem e2 base)
  | GreaterElem(e1,e2)                 -> (get_vars_elem e1 base) @@ (get_vars_elem e2 base)
  | Eq(exp)                            -> (get_vars_eq exp base)
  | InEq(exp)                          -> (get_vars_ineq exp base)
  | BoolVar v                          -> (base v) @@
                                            (match V.parameter v with
                                             | V.Shared -> V.VarSet.empty
                                             | V.Local t -> base t)
  | BoolArrayRd(arr,t)                 -> (get_vars_array arr base)
  | PC (pc,t,_)                        -> (match t with
                                           | V.Shared -> V.VarSet.empty
                                           | V.Local ti -> base ti)
  | PCUpdate (pc,t)                    -> get_vars_tid t base
  | PCRange (pc1,pc2,t,_)              -> (match t with
                                           | V.Shared -> V.VarSet.empty
                                           | V.Local ti -> base ti)


and get_vars_eq ((t1,t2):eq) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  (get_vars_term t1 base) @@ (get_vars_term t2 base)


and get_vars_ineq ((t1,t2):diseq)
                   (base:V.t -> V.VarSet.t) : V.VarSet.t =
  (get_vars_term t1 base) @@ (get_vars_term t2 base)


and get_vars_fs () = Formula.make_fold
                       Formula.GenericLiteralFold
                       (fun base a -> get_vars_atom a base)
                       (fun info -> V.VarSet.empty)
                       (V.VarSet.union)

and get_vars_formula (phi:formula) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  Formula.formula_fold (get_vars_fs()) base phi

(*
and get_vars_literal (l:literal)
                     (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match l with
    Atom a    -> get_vars_atom a base
  | NegAtom a -> get_vars_atom a base


and get_vars_conjunctive_formula (phi:conjunctive_formula) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match phi with
    FalseConj -> V.VarSet.empty
  | TrueConj  -> V.VarSet.empty
  | Conj ls   -> List.fold_left (fun xs l -> (get_vars_literal l base)@@xs) V.VarSet.empty ls


and get_vars_formula (phi:formula) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  match phi with
    Literal(lit)          -> (get_vars_literal lit base)
  | True                  -> V.VarSet.empty
  | False                 -> V.VarSet.empty
  | And(f1,f2)            -> (get_vars_formula f1 base) @@
                             (get_vars_formula f2 base)
  | Or(f1,f2)             -> (get_vars_formula f1 base) @@
                             (get_vars_formula f2 base)
  | Not(f)                -> (get_vars_formula f base)
  | Implies(f1,f2)        -> (get_vars_formula f1 base) @@
                             (get_vars_formula f2 base)
  | Iff (f1,f2)           -> (get_vars_formula f1 base) @@
                             (get_vars_formula f2 base)
*)


(* Exported vars functions *)

let get_vars_as_set (phi:formula) (base:V.t -> V.VarSet.t) : V.VarSet.t =
  let var_set = V.VarSet.fold (fun v set ->
                  V.VarSet.add (V.unprime v) set
                ) (get_vars_formula phi base) (V.VarSet.empty)
  in
    var_set


let get_vars (phi:formula) (base:V.t -> V.VarSet.t) : V.t list =
  V.VarSet.elements (get_vars_as_set phi base)


let filtering_condition (f:V.t -> bool) (v:V.t) : V.VarSet.t =
  if f v then V.VarSet.singleton v else V.VarSet.empty


let primed_vars (f:formula) : V.t list =
  get_vars f (filtering_condition V.is_primed)


let all_vars (f:formula) : V.t list =
  get_vars f (fun v -> V.VarSet.singleton v)


let all_vars_as_set (f:formula) : V.VarSet.t =
  get_vars_as_set f (fun v -> V.VarSet.singleton v)


let all_local_vars (f:formula) : V.t list =
  get_vars f (filtering_condition V.is_local)


let all_global_vars (f:formula) : V.t list =
  get_vars f (filtering_condition V.is_global)


(* Primes in phi the variables modified in ante *)
let prime_modified (rho:formula) (phi:formula) : formula =
(*  LOG "Entering prime_modified" LEVEL TRACE; *)
  let base_f = fun v -> if V.is_primed v then
                          V.VarSet.singleton v
                        else V.VarSet.empty in
  let rec analyze_fs () = Formula.make_fold
                            Formula.GenericLiteralFold
                            (fun info a -> analyze_atom a)
														(fun info -> (V.VarSet.empty, false))
														(fun (s1,b1) (s2,b2) -> (V.VarSet.union s1 s2, b1 || b2))

	and analyze_formula (phi:formula) : (V.VarSet.t * bool) =
    Formula.formula_fold (analyze_fs()) () phi

(*
  let rec analyze_formula (phi:formula) : V.VarSet.t =
    match phi with
    | Literal l -> analyze_literal l
    | True -> V.VarSet.empty
    | False -> V.VarSet.empty
    | And (phi1,phi2) -> V.VarSet.union (analyze_formula phi1) (analyze_formula phi2)
    | Or (phi1,phi2) -> V.VarSet.union (analyze_formula phi1) (analyze_formula phi2)
    | Not phi1 -> analyze_formula phi1
    | Implies (phi1,phi2) -> V.VarSet.union (analyze_formula phi1) (analyze_formula phi2)
    | Iff (phi1,phi2) -> V.VarSet.union (analyze_formula phi1) (analyze_formula phi2)
  and analyze_literal (lit:literal) : V.VarSet.t =
    match lit with
    | Atom a -> analyze_atom a
    | NegAtom a -> analyze_atom a
*)
	and analyze_atom (a:atom) : (V.VarSet.t * bool) =
		match a with
    | Eq (ArrayT (VarArray v), ArrayT (ArrayUp (aa,t,e)))
    | Eq (ArrayT (ArrayUp (aa,t,e)), ArrayT (VarArray v)) ->
				(V.VarSet.singleton (V.set_param (V.unprime v) (V.Local (voc_to_var t))), false)
		| PC(_,_,true)
		| PCUpdate _
		| PCRange (_,_,_,true) -> (V.VarSet.empty, true)
		| _ -> (get_vars_atom a base_f, false) in
	let (pSet,pPC) = analyze_formula rho in
	let p_set = V.VarSet.fold (fun v set ->
                 V.VarSet.add (V.unprime v) set
							 ) pSet V.VarSet.empty in
		prime_only p_set pPC phi


let prime_modified_term (ante:formula) (t:term) : term =
  let p_vars = primed_vars ante in
  let p_set  = V.varset_from_list p_vars
  in
    prime_term_only p_set t




(* CONVERSION FUNCTIONS *)

let rec array_var_from_term (t:term) (prime:bool) : arrays =
  let modif_var v = if prime then (V.prime v) else v in
  match t with
    VarT v                       -> VarArray (modif_var v)
  | SetT(VarSet v)               -> VarArray (modif_var v)
  | ElemT(VarElem v)             -> VarArray (modif_var v)
  | TidT(VarTh v)               -> VarArray (modif_var v)
  | AddrT(VarAddr v)             -> VarArray (modif_var v)
  | CellT(VarCell v)             -> VarArray (modif_var v)
  | SetThT(VarSetTh v)           -> VarArray (modif_var v)
  | PathT(VarPath v)             -> VarArray (modif_var v)
  | MemT(VarMem v)               -> VarArray (modif_var v)
  | IntT(VarInt v)               -> VarArray (modif_var v)
  | ArrayT(VarArray v)           -> VarArray (modif_var v)
  | ElemT(CellData(VarCell v))   -> VarArray (modif_var v)
  | AddrT(Next(VarCell v))       -> VarArray (modif_var v)
  | TidT(CellLockId(VarCell v)) -> VarArray (modif_var v)
  | _ -> Interface.Err.msg "Invalid argument" $
           sprintf "A non variable or cell field term was \
                    passed to function \"array_var_from_term\". \
                    A variable was expected, but \"%s\" was given."
                    (term_to_str t);
         raise(Invalid_argument)


(* Returns scope of a term. If the term is a variable, returns:
    Some "" if is a global variable declaration
    Some p if is a local declaration to process p
    None if the term is not a variable and thus it couldn't be determined *)
let get_term_scope (t:term) : string option =
  try
    match V.scope (term_to_var t) with
    | V.GlobalScope -> Some ""
    | V.Scope p     -> Some p
  with
    No_variable_term _ -> None


let is_global (t:term) : bool =
  get_term_scope t == Some ""


let is_local (t:term) : bool =
  match (get_term_scope t) with
    Some p  -> p <> ""
  | _       -> false


let cons_arrayRd_eq_from_var (s:sort)
                             (th_p:tid)
                             (arr:arrays)
                             (e:initVal_t option) : formula list =
  let cons_array (s:sort) (v_term:term) =
    let v_id = term_id v_term in
    let pr = term_primed v_term in
    let p = term_scope v_term in
    let k = term_nature v_term in
    VarArray (build_var v_id s pr V.Shared p ~nature:k)
  in
  match e with
    Some (Equality t) ->
      begin
        match s with
          Set   -> [eq_term (SetT   (SetArrayRd   (arr, th_p))) t]
        | Elem  -> [eq_term (ElemT  (ElemArrayRd  (arr, th_p))) t]
        | Tid   -> [eq_term (TidT   (TidArrayRd  (arr, th_p))) t]
        | Addr  -> [eq_term (AddrT  (AddrArrayRd  (arr, th_p))) t]
        | Cell  -> [eq_term (CellT  (CellArrayRd  (arr, th_p))) t]
        | SetTh -> [eq_term (SetThT (SetThArrayRd (arr, th_p))) t]
        | SetInt-> [eq_term (SetIntT(SetIntArrayRd(arr, th_p))) t]
        | Path  -> [eq_term (PathT  (PathArrayRd  (arr, th_p))) t]
        | Mem   -> [eq_term (MemT   (MemArrayRd   (arr, th_p))) t]
        | Int   -> [eq_term (IntT   (IntArrayRd   (arr, th_p))) t]
        | _     -> Interface.Err.msg "Invalid argument" $
                           sprintf "By now it is impossible to \
                                    build an array of arrays.";
                   raise(Invalid_argument)
      end
  | Some (Condition c) ->
    begin
      match c with
        F.Iff (F.Literal (F.Atom (BoolVar v)), f) ->
          [F.Iff(F.Literal(F.Atom(BoolArrayRd (VarArray(V.unparam v), th_p))), f)]
      | F.Literal (F.Atom (In (a,s)))           ->
          [exp_in (AddrArrayRd(cons_array Addr (AddrT a), th_p)) s]
      | F.Literal (F.Atom (SubsetEq (s1,s2)))   ->
          [exp_subset (SetArrayRd (cons_array Set (SetT s1), th_p)) s2]
      | F.Literal (F.Atom (InTh (t,s)))         ->
          [exp_inth (TidArrayRd(cons_array Tid (TidT t), th_p)) s]
      | F.Literal (F.Atom (SubsetEqTh (s1,s2))) ->
          [exp_subsetth (SetThArrayRd (cons_array SetTh (SetThT s1),th_p)) s2]
      | F.Literal (F.Atom (InInt (i,s)))        ->
          [exp_inint (IntArrayRd (cons_array Int (IntT i), th_p)) s]
      | F.Literal (F.Atom (SubsetEqInt (s1,s2))) ->
          [exp_subsetint(SetIntArrayRd(cons_array SetInt (SetIntT s1),th_p)) s2]
      | F.Literal (F.Atom (Less (i1,i2)))       ->
          [exp_less (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | F.Literal (F.Atom (Greater (i1,i2)))    ->
          [exp_greater (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | F.Literal (F.Atom (LessEq (i1,i2)))     ->
          [exp_lesseq (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | F.Literal (F.Atom (GreaterEq (i1,i2)))  ->
          [exp_greatereq (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | _                                   -> [c]
    end
  | None -> []


let get_tid_in (v:V.t) : ThreadSet.t =
  match V.parameter v with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


(* VOCABULARY FUNCTIONS *)
let (@@) = ThreadSet.union

let rec voc_term (expr:term) : ThreadSet.t =
  match expr with
    VarT v -> (match V.sort v with
                  Tid -> ThreadSet.singleton (VarTh v)
                | _    -> ThreadSet.empty
              ) @@ get_tid_in v
    | SetT(set)         -> voc_set set
    | AddrT(addr)       -> voc_addr addr
    | ElemT(elem)       -> voc_elem elem
    | TidT(th)          -> voc_tid th
    | CellT(cell)       -> voc_cell cell
    | SetThT(setth)     -> voc_setth setth
    | SetIntT(setint)   -> voc_setint setint
    | SetElemT(setelem) -> voc_setelem setelem
    | PathT(path)       -> voc_path path
    | MemT(mem)         -> voc_mem mem
    | IntT(i)           -> voc_int i
    | ArrayT(arr)       -> voc_array arr
    | AddrArrayT(arr)   -> voc_addrarr arr
    | TidArrayT(arr)    -> voc_tidarr arr


and voc_expr (e:expr_t) : ThreadSet.t =
  match e with
    Term t    -> voc_term t
  | Formula b -> voc_formula b


and voc_array (a:arrays) : ThreadSet.t =
  match a with
    VarArray v       -> get_tid_in v
  | ArrayUp(arr,t,e) -> (voc_array arr) @@ (voc_expr e)


and voc_addrarr (a:addrarr) : ThreadSet.t =
  match a with
    VarAddrArray v       -> get_tid_in v
  | AddrArrayUp(arr,i,a) -> (voc_addrarr arr) @@ (voc_int i) @@ (voc_addr a)
  | CellArr c            -> (voc_cell c)


and voc_tidarr (a:tidarr) : ThreadSet.t =
  match a with
    VarTidArray v       -> get_tid_in v
  | TidArrayUp(arr,i,t) -> (voc_tidarr arr) @@ (voc_int i) @@ (voc_tid t)
  | CellTids c            -> (voc_cell c)


and voc_set (e:set) : ThreadSet.t =
  match e with
    VarSet v             -> get_tid_in v
  | EmptySet             -> ThreadSet.empty
  | Singl(addr)          -> (voc_addr addr)
  | Union(s1,s2)         -> (voc_set s1) @@ (voc_set s2)
  | Intr(s1,s2)          -> (voc_set s1) @@ (voc_set s2)
  | Setdiff(s1,s2)       -> (voc_set s1) @@ (voc_set s2)
  | PathToSet(path)      -> (voc_path path)
  | AddrToSet(mem,addr)  -> (voc_mem mem) @@ (voc_addr addr)
  | AddrToSetAt(mem,a,l) -> (voc_mem mem) @@ (voc_addr a) @@ (voc_int l)
  | SetArrayRd(arr,t)    -> (voc_array arr)


and voc_addr (a:addr) : ThreadSet.t =
  match a with
    VarAddr v                 -> get_tid_in v
  | Null                      -> ThreadSet.empty
  | Next(cell)                -> (voc_cell cell)
  | NextAt(cell,l)            -> (voc_cell cell) @@ (voc_int l)
  | ArrAt(cell,l)             -> (voc_cell cell) @@ (voc_int l)
  | FirstLocked(mem,path)     -> (voc_mem mem) @@ (voc_path path)
  | FirstLockedAt(mem,path,l) -> (voc_mem mem) @@ (voc_path path) @@ (voc_int l)
  | AddrArrayRd(arr,t)        -> (voc_array arr)
  | AddrArrRd(arr,l)          -> (voc_addrarr arr) @@ (voc_int l)


and voc_elem (e:elem) : ThreadSet.t =
  match e with
    VarElem v          -> get_tid_in v
  | CellData(cell)     -> (voc_cell cell)
  | ElemArrayRd(arr,t) -> (voc_array arr)
  | HavocListElem      -> ThreadSet.empty
  | HavocSkiplistElem  -> ThreadSet.empty
  | LowestElem         -> ThreadSet.empty
  | HighestElem        -> ThreadSet.empty


and voc_tid (th:tid) : ThreadSet.t =
  match th with
    VarTh v              -> ThreadSet.add th (get_tid_in v)
  | NoTid               -> ThreadSet.empty
  | CellLockId(cell)     -> (voc_cell cell)
  | CellLockIdAt(cell,l) -> (voc_cell cell) @@ (voc_int l)
  | TidArrayRd(arr,t)   -> (voc_array arr)
  | TidArrRd(arr,l)     -> (voc_tidarr arr) @@ (voc_int l)


and voc_cell (c:cell) : ThreadSet.t =
  let fold f xs = List.fold_left (fun ys x -> (f x) @@ ys) ThreadSet.empty xs in
  match c with
    VarCell v              -> get_tid_in v
  | Error                  -> ThreadSet.empty
  | MkCell(data,addr,th)   -> (voc_elem data) @@
                              (voc_addr addr) @@
                              (voc_tid th)
  | MkSLKCell(data,aa,tt)  -> (voc_elem data)    @@
                              (fold voc_addr aa) @@
                              (fold voc_tid tt)
  | MkSLCell(data,aa,ta,l) -> (voc_elem data)  @@
                              (voc_addrarr aa) @@
                              (voc_tidarr ta ) @@
                              (voc_int l)
  | CellLock(cell,t)       -> (voc_cell cell) @@ (voc_tid t)
  | CellLockAt(cell,l,t)   -> (voc_cell cell) @@ (voc_int l) @@ (voc_tid t)
  | CellUnlock(cell)       -> (voc_cell cell)
  | CellUnlockAt(cell,l)   -> (voc_cell cell) @@ (voc_int l)
  | CellAt(mem,addr)       -> (voc_mem mem) @@ (voc_addr addr)
  | CellArrayRd(arr,t)     -> (voc_array arr)
  | UpdCellAddr(c,i,a)     -> (voc_cell c) @@ (voc_int i) @@ (voc_addr a)


and voc_setth (s:setth) : ThreadSet.t =
  match s with
    VarSetTh v          -> get_tid_in v
  | EmptySetTh          -> ThreadSet.empty
  | SinglTh(th)         -> (voc_tid th)
  | UnionTh(s1,s2)      -> (voc_setth s1) @@ (voc_setth s2)
  | IntrTh(s1,s2)       -> (voc_setth s1) @@ (voc_setth s2)
  | SetdiffTh(s1,s2)    -> (voc_setth s1) @@ (voc_setth s2)
  | SetThArrayRd(arr,t) -> (voc_array arr)


and voc_setint (s:setint) : ThreadSet.t =
  match s with
    VarSetInt v          -> get_tid_in v
  | EmptySetInt          -> ThreadSet.empty
  | SinglInt(th)         -> (voc_int th)
  | UnionInt(s1,s2)      -> (voc_setint s1) @@ (voc_setint s2)
  | IntrInt(s1,s2)       -> (voc_setint s1) @@ (voc_setint s2)
  | SetdiffInt(s1,s2)    -> (voc_setint s1) @@ (voc_setint s2)
  | SetIntArrayRd(arr,t) -> (voc_array arr)


and voc_setelem (s:setelem) : ThreadSet.t =
  match s with
    VarSetElem v          -> get_tid_in v
  | EmptySetElem          -> ThreadSet.empty
  | SinglElem(e)          -> (voc_elem e)
  | UnionElem(s1,s2)      -> (voc_setelem s1) @@ (voc_setelem s2)
  | IntrElem(s1,s2)       -> (voc_setelem s1) @@ (voc_setelem s2)
  | SetdiffElem(s1,s2)    -> (voc_setelem s1) @@ (voc_setelem s2)
  | SetToElems(s,m)       -> (voc_set s) @@ (voc_mem m)
  | SetElemArrayRd(arr,t) -> (voc_array arr)


and voc_path (p:path) : ThreadSet.t =
  match p with
    VarPath v                    -> get_tid_in v
  | Epsilon                      -> ThreadSet.empty
  | SimplePath(addr)             -> (voc_addr addr)
  | GetPath(mem,a_from,a_to)     -> (voc_mem mem) @@
                                    (voc_addr a_from) @@
                                    (voc_addr a_to)
  | GetPathAt(mem,a_from,a_to,l) -> (voc_mem mem) @@
                                    (voc_addr a_from) @@
                                    (voc_addr a_to) @@
                                    (voc_int l)
  | PathArrayRd(arr,t)           -> (voc_array arr)


and voc_mem (m:mem) : ThreadSet.t =
  match m with
    VarMem v             -> get_tid_in v
  | Update(mem,add,cell) -> (voc_mem mem) @@ (voc_addr add) @@ (voc_cell cell)
  | MemArrayRd(arr,t)    -> (voc_array arr)


and voc_int (i:integer) : ThreadSet.t =
  match i with
    IntVal(i)         -> ThreadSet.empty
  | VarInt v          -> get_tid_in v
  | IntNeg(i)         -> (voc_int i)
  | IntAdd(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntSub(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntMul(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntDiv(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntArrayRd(arr,t) -> (voc_array arr)
  | IntSetMin(s)      -> (voc_setint s)
  | IntSetMax(s)      -> (voc_setint s)
  | CellMax(c)        -> (voc_cell c)
  | HavocLevel        -> ThreadSet.empty


and voc_atom (a:atom) : ThreadSet.t =
  match a with
    Append(p1,p2,pres)                 -> (voc_path p1) @@
                                          (voc_path p2) @@
                                          (voc_path pres)
  | Reach(h,add_from,add_to,p)         -> (voc_mem h) @@
                                          (voc_addr add_from) @@
                                          (voc_addr add_to) @@
                                          (voc_path p)
  | ReachAt(h,a_from,a_to,l,p)         -> (voc_mem h) @@
                                          (voc_addr a_from) @@
                                          (voc_addr a_to) @@
                                          (voc_int l) @@
                                          (voc_path p)
  | OrderList(h,a_from,a_to)           -> (voc_mem h) @@
                                          (voc_addr a_from) @@
                                          (voc_addr a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> (voc_mem h) @@
                                          (voc_set s) @@
                                          (voc_int l) @@
                                          (voc_addr a_from) @@
                                          (voc_addr a_to) @@
                                          (voc_setelem elems)
  | In(a,s)                            -> (voc_addr a) @@ (voc_set s)
  | SubsetEq(s_in,s_out)               -> (voc_set s_in) @@ (voc_set s_out)
  | InTh(th,s)                         -> (voc_tid th) @@ (voc_setth s)
  | SubsetEqTh(s_in,s_out)             -> (voc_setth s_in) @@ (voc_setth s_out)
  | InInt(i,s)                         -> (voc_int i) @@ (voc_setint s)
  | SubsetEqInt(s_in,s_out)            -> (voc_setint s_in) @@ (voc_setint s_out)
  | InElem(e,s)                        -> (voc_elem e) @@ (voc_setelem s)
  | SubsetEqElem(s_in,s_out)           -> (voc_setelem s_in) @@ (voc_setelem s_out)
  | Less(i1,i2)                        -> (voc_int i1) @@ (voc_int i2)
  | Greater(i1,i2)                     -> (voc_int i1) @@ (voc_int i2)
  | LessEq(i1,i2)                      -> (voc_int i1) @@ (voc_int i2)
  | GreaterEq(i1,i2)                   -> (voc_int i1) @@ (voc_int i2)
  | LessTid(t1,t2)                     -> (voc_tid t1) @@ (voc_tid t2)
  | LessElem(e1,e2)                    -> (voc_elem e1) @@ (voc_elem e2)
  | GreaterElem(e1,e2)                 -> (voc_elem e1) @@ (voc_elem e2)
  | Eq(exp)                            -> (voc_eq exp)
  | InEq(exp)                          -> (voc_ineq exp)
  | BoolVar v                          -> get_tid_in v
  | BoolArrayRd(arr,t)                 -> (voc_array arr)
  | PC (pc,t,_)                        -> (match t with
                                           | V.Shared -> ThreadSet.empty
                                           | V.Local ti -> ThreadSet.singleton (VarTh ti))
  | PCUpdate (pc,t)                    -> ThreadSet.singleton t
  | PCRange (pc1,pc2,t,_)              -> (match t with
                                           | V.Shared -> ThreadSet.empty
                                           | V.Local ti -> ThreadSet.singleton (VarTh ti))

and voc_eq ((t1,t2):eq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


and voc_ineq ((t1,t2):diseq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


and voc_fs () = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun info a -> voc_atom a)
                  (fun info -> ThreadSet.empty)
                  (@@)


and voc_formula (phi:formula) : ThreadSet.t =
  Formula.formula_fold (voc_fs()) () phi
(*
and voc_literal (l:literal) : tid list =
  match l with
    Atom a    -> voc_atom a
  | NegAtom a -> voc_atom a


and voc_conjunctive_formula (cf:conjunctive_formula) : tid list =
  match cf with
    FalseConj -> []
  | TrueConj  -> []
  | Conj ls   -> List.fold_left (fun xs l -> (voc_literal l)@xs) [] ls


and voc_formula (phi:formula) : tid list =
    match phi with
      Literal(lit)          -> (voc_literal lit)
    | True                  -> []
    | False                 -> []
    | And(f1,f2)            -> (voc_formula f1) @ (voc_formula f2)
    | Or(f1,f2)             -> (voc_formula f1) @ (voc_formula f2)
    | Not(f)                -> (voc_formula f)
    | Implies(f1,f2)        -> (voc_formula f1) @ (voc_formula f2)
    | Iff (f1,f2)           -> (voc_formula f1) @ (voc_formula f2)
*)

(*
let all_voc (phi:formula) : ThreadSet.t =
  let th_list = voc_formula phi in
  let th_set  = List.fold_left (fun set e -> ThreadSet.add e set)
                               (ThreadSet.empty)
                               (th_list)
  in
    th_set
*)


let voc (phi:formula) : ThreadSet.t =
  voc_formula phi
(*
  ThreadSet.elements (all_voc phi)
*)


let unprimed_voc (phi:formula) : ThreadSet.t =
  ThreadSet.filter (is_primed_tid>>not) (voc phi)
(*
  let voc_set = ThreadSet.filter (is_primed_tid>>not) (voc phi)
  in
    ThreadSet.elements voc_set
*)


(* GHOST TERMS *)
let rec var_kind_term (kind:var_nature) (expr:term) : term list =
  match expr with
      VarT v            -> if var_nature v = kind then [expr] else []
    | SetT(set)         -> var_kind_set kind set
    | AddrT(addr)       -> var_kind_addr kind addr
    | ElemT(elem)       -> var_kind_elem kind elem
    | TidT(th)         -> var_kind_tid kind th
    | CellT(cell)       -> var_kind_cell kind cell
    | SetThT(setth)     -> var_kind_setth kind setth
    | SetIntT(setint)   -> var_kind_setint kind setint
    | SetElemT(setelem) -> var_kind_setelem kind setelem
    | PathT(path)       -> var_kind_path kind path
    | MemT(mem)         -> var_kind_mem kind mem
    | IntT(i)           -> var_kind_int kind i
    | ArrayT(arr)       -> var_kind_array kind arr
    | AddrArrayT(arr)   -> var_kind_addrarr kind arr
    | TidArrayT(arr)    -> var_kind_tidarr kind arr


and var_kind_expr (kind:var_nature) (e:expr_t) : term list =
  match e with
    Term t    -> var_kind_term kind t
  | Formula b -> var_kind_formula kind b


and var_kind_array (kind:var_nature) (a:arrays) : term list =
  match a with
    VarArray v       -> if var_nature v = kind then [ArrayT a] else []
  | ArrayUp(arr,t,e) -> (var_kind_array kind arr) @ (var_kind_expr kind e)


and var_kind_addrarr (kind:var_nature) (a:addrarr) : term list =
  match a with
    VarAddrArray v       -> if var_nature v = kind then [AddrArrayT a] else []
  | AddrArrayUp(arr,i,a) -> (var_kind_addrarr kind arr) @
                            (var_kind_int kind i)       @
                            (var_kind_addr kind a)
  | CellArr c            -> (var_kind_cell kind c)


and var_kind_tidarr (kind:var_nature) (a:tidarr) : term list =
  match a with
    VarTidArray v       -> if var_nature v = kind then [TidArrayT a] else []
  | TidArrayUp(arr,i,t) -> (var_kind_tidarr kind arr) @
                           (var_kind_int kind i)      @
                           (var_kind_tid kind t)
  | CellTids c            -> (var_kind_cell kind c)


and var_kind_set (kind:var_nature) (e:set) : term list =
  match e with
    VarSet v            -> if var_nature v = kind then [SetT e] else []
  | EmptySet            -> []
  | Singl(addr)         -> (var_kind_addr kind addr)
  | Union(s1,s2)        -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | Intr(s1,s2)         -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | Setdiff(s1,s2)      -> (var_kind_set kind s1) @ (var_kind_set kind s2)
  | PathToSet(path)     -> (var_kind_path kind path)
  | AddrToSet(mem,addr) -> (var_kind_mem kind mem) @ (var_kind_addr kind addr)
  | AddrToSetAt(mem,a,l)-> (var_kind_mem kind mem) @
                           (var_kind_addr kind a)  @
                           (var_kind_int kind l)
  | SetArrayRd(arr,t)   -> (var_kind_array kind arr)


and var_kind_addr (kind:var_nature) (a:addr) : term list =
  match a with
    VarAddr v                 -> if var_nature v = kind then [AddrT a] else []
  | Null                      -> []
  | Next(cell)                -> (var_kind_cell kind cell)
  | NextAt(cell,l)            -> (var_kind_cell kind cell) @ (var_kind_int kind l)
  | ArrAt(cell,l)             -> (var_kind_cell kind cell) @ (var_kind_int kind l)
  | FirstLocked(mem,path)     -> (var_kind_mem kind mem) @
                                 (var_kind_path kind path)
  | FirstLockedAt(mem,path,l) -> (var_kind_mem kind mem)   @
                                 (var_kind_path kind path) @
                                 (var_kind_int kind l)
  | AddrArrayRd(arr,t)        -> (var_kind_array kind arr)
  | AddrArrRd(arr,l)          -> (var_kind_addrarr kind arr) @ (var_kind_int kind l)


and var_kind_elem (kind:var_nature) (e:elem) : term list =
  match e with
    VarElem v          -> if var_nature v = kind then [ElemT e] else []
  | CellData(cell)     -> (var_kind_cell kind cell)
  | ElemArrayRd(arr,t) -> (var_kind_array kind arr)
  | HavocListElem      -> []
  | HavocSkiplistElem  -> []
  | LowestElem         -> []
  | HighestElem        -> []


and var_kind_tid (kind:var_nature) (th:tid) : term list =
  match th with
    VarTh v              -> if var_nature v = kind then [TidT th] else []
  | NoTid               -> []
  | CellLockId(cell)     -> (var_kind_cell kind cell)
  | CellLockIdAt(cell,l) -> (var_kind_cell kind cell) @ (var_kind_int kind l)
  | TidArrayRd(arr,t)   -> (var_kind_array kind arr)
  | TidArrRd(arr,l)     -> (var_kind_tidarr kind arr) @ (var_kind_int kind l)


and var_kind_cell (kind:var_nature) (c:cell) : term list =
  let fold f xs = List.fold_left (fun ys x -> (f kind x) @ ys) [] xs in
  match c with
    VarCell v              -> if var_nature v = kind then [CellT c] else []
  | Error                  -> []
  | MkCell(data,addr,th)   -> (var_kind_elem kind data) @
                              (var_kind_addr kind addr) @
                              (var_kind_tid kind th)
  | MkSLKCell(data,aa,tt)  -> (var_kind_elem kind data)  @
                              (fold var_kind_addr aa)    @
                              (fold var_kind_tid tt)
  | MkSLCell(data,aa,ta,l) -> (var_kind_elem kind data)  @
                              (var_kind_addrarr kind aa) @
                              (var_kind_tidarr kind ta)  @
                              (var_kind_int kind l)
  | CellLock(cell,t)       -> (var_kind_cell kind cell) @
                              (var_kind_tid kind t)
  | CellLockAt(cell,l,t)   -> (var_kind_cell kind cell) @
                              (var_kind_int kind l)     @
                              (var_kind_tid kind t)
  | CellUnlock(cell)       -> (var_kind_cell kind cell)
  | CellUnlockAt(cell,l)   -> (var_kind_cell kind cell) @
                              (var_kind_int kind l)
  | CellAt(mem,addr)       -> (var_kind_mem kind mem) @
                              (var_kind_addr kind addr)
  | CellArrayRd(arr,t)     -> (var_kind_array kind arr)
  | UpdCellAddr(c,i,a)     -> (var_kind_cell kind c) @
                              (var_kind_int kind i)  @
                              (var_kind_addr kind a)


and var_kind_setth (kind:var_nature) (s:setth) : term list =
  match s with
    VarSetTh v          -> if var_nature v = kind then [SetThT s] else []
  | EmptySetTh          -> []
  | SinglTh(th)         -> (var_kind_tid kind th)
  | UnionTh(s1,s2)      -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | IntrTh(s1,s2)       -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetdiffTh(s1,s2)    -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetThArrayRd(arr,t) -> (var_kind_array kind arr)


and var_kind_setint (kind:var_nature) (s:setint) : term list =
  match s with
    VarSetInt v          -> if var_nature v = kind then [SetIntT s] else []
  | EmptySetInt          -> []
  | SinglInt(i)          -> (var_kind_int kind i)
  | UnionInt(s1,s2)      -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | IntrInt(s1,s2)       -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetdiffInt(s1,s2)    -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetIntArrayRd(arr,t) -> (var_kind_array kind arr)


and var_kind_setelem (kind:var_nature) (s:setelem) : term list =
  match s with
    VarSetElem v          -> if var_nature v = kind then [SetElemT s] else []
  | EmptySetElem          -> []
  | SinglElem(e)          -> (var_kind_elem kind e)
  | UnionElem(s1,s2)      -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | IntrElem(s1,s2)       -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | SetdiffElem(s1,s2)    -> (var_kind_setelem kind s1) @
                             (var_kind_setelem kind s2)
  | SetToElems(s,m)       -> (var_kind_set kind s) @ (var_kind_mem kind m)
  | SetElemArrayRd(arr,t) -> (var_kind_array kind arr)


and var_kind_path (kind:var_nature) (p:path) : term list =
  match p with
    VarPath v                        -> if var_nature v= kind then [PathT p] else []
  | Epsilon                          -> []
  | SimplePath(addr)                 -> (var_kind_addr kind addr)
  | GetPath(mem,add_from,add_to)     -> (var_kind_mem kind mem) @
                                        (var_kind_addr kind add_from) @
                                        (var_kind_addr kind add_to)
  | GetPathAt(mem,add_from,add_to,l) -> (var_kind_mem kind mem) @
                                        (var_kind_addr kind add_from) @
                                        (var_kind_addr kind add_to) @
                                        (var_kind_int kind l)
  | PathArrayRd(arr,t)               -> (var_kind_array kind arr)


and var_kind_mem (kind:var_nature) (m:mem) : term list =
  match m with
    VarMem v             -> if var_nature v = kind then [MemT m] else []
  | Update(mem,add,cell) -> (var_kind_mem kind mem) @
                            (var_kind_addr kind add) @
                            (var_kind_cell kind cell)
  | MemArrayRd(arr,t)    -> (var_kind_array kind arr)


and var_kind_int (kind:var_nature) (i:integer) : term list =
  match i with
    IntVal(i)         -> []
  | VarInt v          -> if var_nature v = kind then [IntT i] else []
  | IntNeg(i)         -> (var_kind_int kind i)
  | IntAdd(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntSub(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntMul(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntDiv(i1,i2)     -> (var_kind_int kind i1) @ (var_kind_int kind i2)
  | IntArrayRd(arr,t) -> (var_kind_array kind arr)
  | IntSetMin(s)      -> (var_kind_setint kind s)
  | IntSetMax(s)      -> (var_kind_setint kind s)
  | CellMax(c)        -> (var_kind_cell kind c)
  | HavocLevel        -> []


and var_kind_atom (kind:var_nature) (a:atom) : term list =
  match a with
    Append(p1,p2,pres)                 -> (var_kind_path kind p1) @
                                          (var_kind_path kind p2) @
                                          (var_kind_path kind pres)
  | Reach(h,add_from,add_to,p)         -> (var_kind_mem kind h) @
                                          (var_kind_addr kind add_from) @
                                          (var_kind_addr kind add_to) @
                                          (var_kind_path kind p)
  | ReachAt(h,a_from,a_to,l,p)         -> (var_kind_mem kind h) @
                                          (var_kind_addr kind a_from) @
                                          (var_kind_addr kind a_to) @
                                          (var_kind_int kind l) @
                                          (var_kind_path kind p)
  | OrderList(h,a_from,a_to)           -> (var_kind_mem kind h) @
                                          (var_kind_addr kind a_from) @
                                          (var_kind_addr kind a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> (var_kind_mem kind h) @
                                          (var_kind_set kind s) @
                                          (var_kind_int kind l) @
                                          (var_kind_addr kind a_from) @
                                          (var_kind_addr kind a_to) @
                                          (var_kind_setelem kind elems)
  | In(a,s)                            -> (var_kind_addr kind a) @ (var_kind_set kind s)
  | SubsetEq(s_in,s_out)               -> (var_kind_set kind s_in) @
                                          (var_kind_set kind s_out)
  | InTh(th,s)                         -> (var_kind_tid kind th) @
                                          (var_kind_setth kind s)
  | SubsetEqTh(s_in,s_out)             -> (var_kind_setth kind s_in) @
                                          (var_kind_setth kind s_out)
  | InInt(i,s)                         -> (var_kind_int kind i) @
                                          (var_kind_setint kind s)
  | SubsetEqInt(s_in,s_out)            -> (var_kind_setint kind s_in) @
                                          (var_kind_setint kind s_out)
  | InElem(e,s)                        -> (var_kind_elem kind e) @
                                          (var_kind_setelem kind s)
  | SubsetEqElem(s_in,s_out)           -> (var_kind_setelem kind s_in) @
                                          (var_kind_setelem kind s_out)
  | Less(i1,i2)                        -> (var_kind_int kind i1) @
                                          (var_kind_int kind i2)
  | Greater(i1,i2)                     -> (var_kind_int kind i1) @
                                          (var_kind_int kind i2)
  | LessEq(i1,i2)                      -> (var_kind_int kind i1) @
                                          (var_kind_int kind i2)
  | GreaterEq(i1,i2)                   -> (var_kind_int kind i1) @
                                          (var_kind_int kind i2)
  | LessTid(t1,t2)                     -> (var_kind_tid kind t1) @
                                          (var_kind_tid kind t2)
  | LessElem(e1,e2)                    -> (var_kind_elem kind e1) @
                                          (var_kind_elem kind e2)
  | GreaterElem(e1,e2)                 -> (var_kind_elem kind e1) @
                                          (var_kind_elem kind e2)
  | Eq(exp)                            -> (var_kind_eq kind exp)
  | InEq(exp)                          -> (var_kind_ineq kind exp)
  | BoolVar v                          -> if var_nature v = kind then
                                            [VarT v]
                                          else
                                            []
  | BoolArrayRd(arr,t)                 -> (var_kind_array kind arr)
  | PC (pc,t,_)                        -> []
  | PCUpdate (_,_)                     -> []
  | PCRange (pc1,pc2,t,_)              -> []


and var_kind_eq (kind:var_nature) ((t1,t2):eq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)


and var_kind_ineq (kind:var_nature) ((t1,t2):diseq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)


and var_kind_fs () = Formula.make_fold
                       Formula.GenericLiteralFold
                       (fun info a -> var_kind_atom info a)
                       (fun info -> [])
                       (@)


and var_kind_formula (kind:var_nature) (phi:formula) : term list =
  Formula.formula_fold (var_kind_fs()) kind phi

(*
and var_kind_literal (kind:var_nature) (l:literal) : term list =
  match l with
    Atom a    -> var_kind_atom kind a
  | NegAtom a -> var_kind_atom kind a


and var_kind_conjunctive_formula (kind:var_nature)
                                 (cf:conjunctive_formula) : term list =
  match cf with
    FalseConj -> []
  | TrueConj  -> []
  | Conj ls   -> List.fold_left (fun xs l -> (var_kind_literal kind l)@xs) [] ls


and var_kind_formula (kind:var_nature) (phi:formula) : term list =
    match phi with
      Literal(lit)       -> (var_kind_literal kind lit)
    | True               -> []
    | False              -> []
    | And(f1,f2)         -> (var_kind_formula kind f1) @
                            (var_kind_formula kind f2)
    | Or(f1,f2)          -> (var_kind_formula kind f1) @
                            (var_kind_formula kind f2)
    | Not(f)             -> (var_kind_formula kind f)
    | Implies(f1,f2)     -> (var_kind_formula kind f1) @
                            (var_kind_formula kind f2)
    | Iff (f1,f2)        -> (var_kind_formula kind f1) @
                            (var_kind_formula kind f2)
*)


let var_kind (kind:var_nature) (e:expr_t) : term list =
  let ghost_list = var_kind_expr kind e in
  let ghost_set = List.fold_left (fun set e -> TermSet.add e set)
                               (TermSet.empty)
                               (ghost_list)
  in
    TermSet.elements ghost_set




(* PARAMETRIZATION FUNCTIONS *)

let rec param_a_term (pfun:V.t option -> V.shared_or_local) (expr:term) : term =
  match expr with
    VarT(v)           -> VarT       (V.set_param v (pfun (Some v)))
  | SetT(set)         -> SetT       (param_set      pfun set    )
  | AddrT(addr)       -> AddrT      (param_addr_aux pfun addr   )
  | ElemT(elem)       -> ElemT      (param_elem_aux pfun elem   )
  | TidT(th)          -> TidT       (param_tid_aux  pfun th     )
  | CellT(cell)       -> CellT      (param_cell_aux pfun cell   )
  | SetThT(setth)     -> SetThT     (param_setth    pfun setth  )
  | SetIntT(setint)   -> SetIntT    (param_setint   pfun setint )
  | SetElemT(setelem) -> SetElemT   (param_setelem  pfun setelem)
  | PathT(path)       -> PathT      (param_path     pfun path   )
  | MemT(mem)         -> MemT       (param_mem      pfun mem    )
  | IntT(i)           -> IntT       (param_int_aux      pfun i      )
  | ArrayT(arr)       -> ArrayT     (param_arrays   pfun arr    )
  | AddrArrayT(arr)   -> AddrArrayT (param_addrarr_aux  pfun arr    )
  | TidArrayT(arr)    -> TidArrayT  (param_tidarr_aux   pfun arr    )


and param_expr_aux (pfun:V.t option -> V.shared_or_local) (expr:expr_t): expr_t =
  match expr with
    Term t    -> Term (param_a_term pfun t)
  | Formula b -> Formula (param_formula pfun b)


and param_arrays (pfun:V.t option -> V.shared_or_local) (arr:arrays) : arrays =
  match arr with
    VarArray v       -> VarArray (V.set_param v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | ArrayUp(arr,t,e) -> ArrayUp(param_arrays pfun arr, t,
                                param_expr_aux pfun e)


and param_addrarr_aux (pfun:V.t option -> V.shared_or_local) (arr:addrarr) : addrarr =
  match arr with
    VarAddrArray v       -> VarAddrArray (V.set_param v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(param_addrarr_aux pfun arr,
                                        param_int_aux pfun i,
                                        param_addr_aux pfun a)
  | CellArr c            -> CellArr (param_cell_aux pfun c)


and param_tidarr_aux (pfun:V.t option -> V.shared_or_local) (arr:tidarr) : tidarr =
  match arr with
    VarTidArray v       -> VarTidArray (V.set_param v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | TidArrayUp(arr,i,t) -> TidArrayUp(param_tidarr_aux pfun arr,
                                      param_int_aux pfun i,
                                      param_tid_aux pfun t)
  | CellTids c            -> CellTids (param_cell_aux pfun c)


and param_set (pfun:V.t option -> V.shared_or_local) (e:set) : set =
  match e with
    VarSet v             -> VarSet (V.set_param v (pfun (Some v)))
  | EmptySet             -> EmptySet
  | Singl(addr)          -> Singl(param_addr_aux pfun addr)
  | Union(s1,s2)         -> Union(param_set pfun s1,
                                  param_set pfun s2)
  | Intr(s1,s2)          -> Intr(param_set pfun s1,
                                 param_set pfun s2)
  | Setdiff(s1,s2)       -> Setdiff(param_set pfun s1,
                                    param_set pfun s2)
  | PathToSet(path)      -> PathToSet(param_path pfun path)
  | AddrToSet(mem,addr)  -> AddrToSet(param_mem pfun mem,
                                      param_addr_aux pfun addr)
  | AddrToSetAt(mem,a,l) -> AddrToSetAt(param_mem pfun mem,
                                        param_addr_aux pfun a,
                                        param_int_aux pfun l)
  | SetArrayRd(arr,t)    -> SetArrayRd(param_arrays pfun arr, t)


and param_addr_aux (pfun:V.t option -> V.shared_or_local) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr (V.set_param v (pfun (Some v)))
  | Null                      -> Null
  | Next(cell)                -> Next(param_cell_aux pfun cell)
  | NextAt(cell,l)            -> NextAt(param_cell_aux pfun cell,
                                        param_int_aux pfun l)
  | ArrAt(cell,l)             -> ArrAt(param_cell_aux pfun cell,
                                       param_int_aux pfun l)
  | FirstLocked(mem,path)     -> FirstLocked(param_mem pfun mem,
                                             param_path pfun path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(param_mem pfun mem,
                                               param_path pfun path,
                                               param_int_aux pfun l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(param_arrays pfun arr, t)
  | AddrArrRd(arr,l)          -> AddrArrRd(param_addrarr_aux pfun arr,
                                           param_int_aux pfun l)


and param_elem_aux (pfun:V.t option -> V.shared_or_local) (e:elem) : elem =
  match e with
    VarElem v            -> VarElem (V.set_param v (pfun (Some v)))
  | CellData(cell)       -> CellData(param_cell_aux pfun cell)
  | ElemArrayRd(arr,t)   -> ElemArrayRd(param_arrays pfun arr, t)
  | HavocListElem        -> HavocListElem
  | HavocSkiplistElem    -> HavocSkiplistElem
  | LowestElem           -> LowestElem
  | HighestElem          -> HighestElem


and param_tid_aux (pfun:V.t option -> V.shared_or_local) (th:tid) : tid =
  match th with
    VarTh v              -> VarTh (V.set_param v (pfun (Some v)))
  | NoTid               -> NoTid
  | CellLockId(cell)     -> CellLockId(param_cell_aux pfun cell)
  | CellLockIdAt(cell,l) -> CellLockIdAt(param_cell_aux pfun cell,
                                         param_int_aux pfun l)
  | TidArrayRd(arr,t)   -> TidArrayRd(param_arrays pfun arr, t)
  | TidArrRd(arr,l)     -> TidArrRd(param_tidarr_aux pfun arr,
                                      param_int_aux pfun l)


and param_cell_aux (pfun:V.t option -> V.shared_or_local) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (V.set_param v (pfun (Some v)))
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(param_elem_aux pfun data,
                                   param_addr_aux pfun addr,
                                   param_tid_aux pfun th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(param_elem_aux pfun data,
                                        List.map (param_addr_aux pfun) aa,
                                        List.map (param_tid_aux pfun) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(param_elem_aux pfun data,
                                       param_addrarr_aux pfun aa,
                                       param_tidarr_aux pfun ta,
                                       param_int_aux pfun l)
  | CellLock(cell,t)       -> CellLock(param_cell_aux pfun cell,
                                       param_tid_aux pfun t)
  | CellLockAt(cell,l, t)  -> CellLockAt(param_cell_aux pfun cell,
                                         param_int_aux pfun l,
                                         param_tid_aux pfun t)
  | CellUnlock(cell)       -> CellUnlock(param_cell_aux pfun cell)
  | CellUnlockAt(cell,l)   -> CellUnlockAt(param_cell_aux pfun cell,
                                           param_int_aux pfun l)
  | CellAt(mem,addr)       -> CellAt(param_mem pfun mem,
                                     param_addr_aux pfun addr)
  | CellArrayRd(arr,t)     -> CellArrayRd(param_arrays pfun arr, t)
  | UpdCellAddr(c,i,a)     -> UpdCellAddr(param_cell_aux pfun c,
                                          param_int_aux pfun i,
                                          param_addr_aux pfun a)


and param_setth (pfun:V.t option -> V.shared_or_local) (s:setth) : setth =
  match s with
    VarSetTh v            -> VarSetTh (V.set_param v (pfun (Some v)))
  | EmptySetTh            -> EmptySetTh
  | SinglTh(th)           -> SinglTh(param_tid_aux pfun th)
  | UnionTh(s1,s2)        -> UnionTh(param_setth pfun s1,
                                     param_setth pfun s2)
  | IntrTh(s1,s2)         -> IntrTh(param_setth pfun s1,
                                    param_setth pfun s2)
  | SetdiffTh(s1,s2)      -> SetdiffTh(param_setth pfun s1,
                                       param_setth pfun s2)
  | SetThArrayRd(arr,t)   -> SetThArrayRd(param_arrays pfun arr, t)


and param_setint (pfun:V.t option -> V.shared_or_local) (s:setint) : setint =
  match s with
    VarSetInt v            -> VarSetInt (V.set_param v (pfun (Some v)))
  | EmptySetInt            -> EmptySetInt
  | SinglInt(i)            -> SinglInt(param_int_aux pfun i)
  | UnionInt(s1,s2)        -> UnionInt(param_setint pfun s1,
                                       param_setint pfun s2)
  | IntrInt(s1,s2)         -> IntrInt(param_setint pfun s1,
                                    param_setint pfun s2)
  | SetdiffInt(s1,s2)      -> SetdiffInt(param_setint pfun s1,
                                       param_setint pfun s2)
  | SetIntArrayRd(arr,t)   -> SetIntArrayRd(param_arrays pfun arr, t)


and param_setelem (pfun:V.t option -> V.shared_or_local) (s:setelem) : setelem =
  match s with
    VarSetElem v            -> VarSetElem (V.set_param v (pfun (Some v)))
  | EmptySetElem            -> EmptySetElem
  | SinglElem(e)            -> SinglElem(param_elem_aux pfun e)
  | UnionElem(s1,s2)        -> UnionElem(param_setelem pfun s1,
                                         param_setelem pfun s2)
  | IntrElem(s1,s2)         -> IntrElem(param_setelem pfun s1,
                                        param_setelem pfun s2)
  | SetdiffElem(s1,s2)      -> SetdiffElem(param_setelem pfun s1,
                                           param_setelem pfun s2)
  | SetToElems(s,m)         -> SetToElems(param_set pfun s, param_mem pfun m)
  | SetElemArrayRd(arr,t)   -> SetElemArrayRd(param_arrays pfun arr, t)


and param_path (pfun:V.t option -> V.shared_or_local) (path:path) : path =
  match path with
    VarPath v                        -> VarPath (V.set_param v (pfun (Some v)))
  | Epsilon                          -> Epsilon
  | SimplePath(addr)                 -> SimplePath(param_addr_aux pfun addr)
  | GetPath(mem,add_from,add_to)     -> GetPath(param_mem pfun mem,
                                                param_addr_aux pfun add_from,
                                                param_addr_aux pfun add_to)
  | GetPathAt(mem,add_from,add_to,l) -> GetPathAt(param_mem pfun mem,
                                                  param_addr_aux pfun add_from,
                                                  param_addr_aux pfun add_to,
                                                  param_int_aux pfun l)
  | PathArrayRd(arr,t)           -> PathArrayRd(param_arrays pfun arr, t)


and param_mem (pfun:V.t option -> V.shared_or_local) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem (V.set_param v (pfun (Some v)))
  | Update(mem,add,cell) -> Update(param_mem pfun mem,
                                   param_addr_aux pfun add,
                                   param_cell_aux pfun cell)
  | MemArrayRd(arr,t)    -> MemArrayRd(param_arrays pfun arr, t)


and param_int_aux (pfun:V.t option -> V.shared_or_local) (i:integer) : integer =
  match i with
    IntVal(i)           -> IntVal(i)
  | VarInt v            -> VarInt (V.set_param v (pfun (Some v)))
  | IntNeg(i)           -> IntNeg(param_int_aux pfun i)
  | IntAdd(i1,i2)       -> IntAdd(param_int_aux pfun i1,
                                  param_int_aux pfun i2)
  | IntSub(i1,i2)       -> IntSub(param_int_aux pfun i1,
                                  param_int_aux pfun i2)
  | IntMul(i1,i2)       -> IntMul(param_int_aux pfun i1,
                                  param_int_aux pfun i2)
  | IntDiv(i1,i2)       -> IntDiv(param_int_aux pfun i1,
                                  param_int_aux pfun i2)
  | IntArrayRd(arr,t)   -> IntArrayRd(param_arrays pfun arr, t)
  | IntSetMin(s)        -> IntSetMin(param_setint pfun s)
  | IntSetMax(s)        -> IntSetMax(param_setint pfun s)
  | CellMax(c)          -> CellMax(param_cell_aux pfun c)
  | HavocLevel          -> HavocLevel


and param_atom (pfun:V.t option -> V.shared_or_local) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                 -> Append(param_path pfun p1,
                                                 param_path pfun p2,
                                                 param_path pfun pres)
  | Reach(h,add_from,add_to,p)         -> Reach(param_mem pfun h,
                                                param_addr_aux pfun add_from,
                                                param_addr_aux pfun add_to,
                                                param_path pfun p)
  | ReachAt(h,a_from,a_to,l,p)         -> ReachAt(param_mem pfun h,
                                                  param_addr_aux pfun a_from,
                                                  param_addr_aux pfun a_to,
                                                  param_int_aux pfun l,
                                                  param_path pfun p)
  | OrderList(h,a_from,a_to)           -> OrderList(param_mem pfun h,
                                                    param_addr_aux pfun a_from,
                                                    param_addr_aux pfun a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Skiplist(param_mem pfun h,
                                                   param_set pfun s,
                                                   param_int_aux pfun l,
                                                   param_addr_aux pfun a_from,
                                                   param_addr_aux pfun a_to,
                                                   param_setelem pfun elems)
  | In(a,s)                            -> In(param_addr_aux pfun a,
                                             param_set pfun s)
  | SubsetEq(s_in,s_out)               -> SubsetEq(param_set pfun s_in,
                                                   param_set pfun s_out)
  | InTh(th,s)                         -> InTh(param_tid_aux pfun th,
                                               param_setth pfun s)
  | SubsetEqTh(s_in,s_out)             -> SubsetEqTh(param_setth pfun s_in,
                                                     param_setth pfun s_out)
  | InInt(i,s)                         -> InInt(param_int_aux pfun i,
                                                param_setint pfun s)
  | SubsetEqInt(s_in,s_out)            -> SubsetEqInt(param_setint pfun s_in,
                                                      param_setint pfun s_out)
  | InElem(e,s)                        -> InElem(param_elem_aux pfun e,
                                                 param_setelem pfun s)
  | SubsetEqElem(s_in,s_out)           -> SubsetEqElem(param_setelem pfun s_in,
                                                       param_setelem pfun s_out)
  | Less(i1,i2)                        -> Less(param_int_aux pfun i1,
                                               param_int_aux pfun i2)
  | Greater(i1,i2)                     -> Greater(param_int_aux pfun i1,
                                                  param_int_aux pfun i2)
  | LessEq(i1,i2)                      -> LessEq(param_int_aux pfun i1,
                                                 param_int_aux pfun i2)
  | GreaterEq(i1,i2)                   -> GreaterEq(param_int_aux pfun i1,
                                                    param_int_aux pfun i2)
  | LessTid(t1,t2)                     -> LessTid(param_tid_aux pfun t1,
                                                  param_tid_aux pfun t2)
  | LessElem(e1,e2)                    -> LessElem(param_elem_aux pfun e1,
                                                   param_elem_aux pfun e2)
  | GreaterElem(e1,e2)                 -> GreaterElem(param_elem_aux pfun e1,
                                                      param_elem_aux pfun e2)
  | Eq(exp)                            -> Eq(param_eq pfun exp)
  | InEq(exp)                          -> InEq(param_ineq pfun exp)
  | BoolVar v                          -> BoolVar (V.set_param v (pfun (Some v)))
  | BoolArrayRd(arr,t)                 -> BoolArrayRd(param_arrays pfun arr, t)
      (* TODO: Fix, not sure if         for open arrays is correct *)
  | PC (pc,_,p)                        -> PC (pc, pfun None, p)
  | PCUpdate (pc,t)                    -> PCUpdate (pc,t)
  | PCRange (pc1,pc2,_,p)              -> PCRange (pc1, pc2, pfun None, p)


and param_fs () = Formula.make_trans
                    Formula.GenericLiteralTrans
                    (fun info a -> param_atom info a)

(*
and param_literal (pfun:V.t option -> V.shared_or_local) (l:literal) : literal =
  match l with
    Atom a    -> Atom    (param_atom pfun a)
  | NegAtom a -> NegAtom (param_atom pfun a)
*)


and param_eq (pfun:V.t option -> V.shared_or_local) ((t1,t2):eq) : eq =
  (param_a_term pfun t1, param_a_term pfun t2)


and param_ineq (pfun:V.t option -> V.shared_or_local) ((t1,t2):diseq) : diseq =
  (param_a_term pfun t1, param_a_term pfun t2)

(*
and param_conjunctive_formula (pfun:V.t option -> V.shared_or_local)
                              (cf:conjunctive_formula) : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (param_literal pfun) ls)
*)


and param_formula (pfun:V.t option -> V.shared_or_local) (phi:formula) : formula =
  Formula.formula_trans (param_fs()) pfun phi

(*
and param_formula (pfun:V.t option -> V.shared_or_local) (phi:formula) : formula =
  match phi with
    Literal(lit)          -> Literal(param_literal pfun lit)
  | True                  -> True
  | False                 -> False
  | And(f1,f2)            -> And(param_formula pfun f1,
                                 param_formula pfun f2)
  | Or(f1,f2)             -> Or(param_formula pfun f1,
                                param_formula pfun f2)
  | Not(f)                -> Not(param_formula pfun f)
  | Implies(f1,f2)        -> Implies(param_formula pfun f1,
                                     param_formula pfun f2)
  | Iff (f1,f2)           -> Iff(param_formula pfun f1,
                                 param_formula pfun f2)
*)


let param_local_only (th_p:V.shared_or_local) (v_opt:V.t option) : V.shared_or_local =
  match v_opt with
    None -> th_p
  | Some v -> if V.is_local v then th_p else V.Shared


let param (th_p:V.shared_or_local) (f:formula) : formula =
  param_formula (param_local_only th_p) f


let param_term (th_p:V.shared_or_local) (t:term) : term =
  param_a_term (param_local_only th_p) t


let param_expr (th_p:V.shared_or_local) (e:expr_t) : expr_t =
  param_expr_aux (param_local_only th_p) e


let param_cell (th_p:V.shared_or_local) (c:cell) : cell =
  param_cell_aux (param_local_only th_p) c


let param_elem (th_p:V.shared_or_local) (e:elem) : elem =
  param_elem_aux (param_local_only th_p) e


let param_addr (th_p:V.shared_or_local) (a:addr) : addr =
  param_addr_aux (param_local_only th_p) a


let param_th (th_p:V.shared_or_local) (t:tid) : tid =
  param_tid_aux (param_local_only th_p) t


let param_int (th_p:V.shared_or_local) (i:integer) : integer =
  param_int_aux (param_local_only th_p) i


let param_addrarr (th_p:V.shared_or_local) (aa:addrarr) : addrarr =
  param_addrarr_aux (param_local_only th_p) aa


let param_tidarr (th_p:V.shared_or_local) (tt:tidarr) : tidarr =
  param_tidarr_aux (param_local_only th_p) tt


let param_variable (th_p:V.shared_or_local) (v:V.t) : V.t =
    V.set_param v (param_local_only th_p (Some v))


(* THREAD SUBSTITUTION FUNCTIONS *)


let new_tid_subst (info:(tid * tid) list) : tid_subst_t = info


let new_multiple_tid_subst (ths:tid list)
                           (assigns:tid list list) : tid_subst_t list =
  let _ = assert (List.for_all (fun l ->
                    let ths_size = List.length ths
                    in
                      List.length l = ths_size
                  ) assigns)
  in
    List.fold_left (fun xs a ->
      (List.combine ths a) :: xs
    ) [] assigns


let new_comb_subst (th_domain:tid list)
                   (th_range:tid  list) : tid_subst_t list =
  let comb_th_domain = choose_range th_domain 1 (List.length th_domain)
  in
    List.flatten $
      List.map (fun xs ->
        let ln = List.length xs in
        let assign_comb = comb th_range ln in
        List.map (fun ys ->
          List.combine xs ys
        ) assign_comb
      ) comb_th_domain


let subst_domain (subst:tid_subst_t) : ThreadSet.t =
  List.fold_left (fun set (d,_) -> ThreadSet.add d set) ThreadSet.empty subst


let subst_codomain (subst:tid_subst_t) : ThreadSet.t =
  List.fold_left (fun set (_,r) -> ThreadSet.add r set) ThreadSet.empty subst


let subst_domain_in (tid_set:ThreadSet.t) (subst:tid_subst_t) : bool =
  List.for_all (fun (d,_) -> ThreadSet.mem d tid_set) subst


let subst_codomain_in (tid_set:ThreadSet.t) (subst:tid_subst_t) : bool =
  List.for_all (fun (_,r) -> ThreadSet.mem r tid_set) subst


let rec subst_shared_or_local (subst: tid_subst_t) (th:V.shared_or_local) : 
  V.shared_or_local =
  match th with
  | V.Shared -> V.Shared
  | V.Local t -> V.Local (voc_to_var (subst_tid_th subst (VarTh t)))
and subst_tid_term (subs:tid_subst_t) (expr:term) : term =
  match expr with
    VarT v              -> VarT (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | SetT(set)           -> SetT(subst_tid_set subs set)
  | AddrT(addr)         -> AddrT(subst_tid_addr subs addr)
  | ElemT(elem)         -> ElemT(subst_tid_elem subs elem)
  | TidT(th)           -> TidT(subst_tid_th subs th)
  | CellT(cell)         -> CellT(subst_tid_cell subs cell)
  | SetThT(setth)       -> SetThT(subst_tid_setth subs setth)
  | SetIntT(setint)     -> SetIntT(subst_tid_setint subs setint)
  | SetElemT(setelem)   -> SetElemT(subst_tid_setelem subs setelem)
  | PathT(path)         -> PathT(subst_tid_path subs path)
  | MemT(mem)           -> MemT(subst_tid_mem subs mem)
  | IntT(i)             -> IntT(subst_tid_int subs i)
  | ArrayT(arr)         -> ArrayT(subst_tid_array subs arr)
  | AddrArrayT(arr)     -> AddrArrayT(subst_tid_addrarr subs arr)
  | TidArrayT(arr)      -> TidArrayT(subst_tid_tidarr subs arr)
and subst_tid_expr (subs:tid_subst_t) (expr:expr_t) : expr_t =
  match expr with
    Term t    -> Term (subst_tid_term subs t)
  | Formula b -> Formula (subst_tid subs b)
and subst_tid_array (subs:tid_subst_t) (expr:arrays) : arrays =
  match expr with
    VarArray v       -> VarArray (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | ArrayUp(arr,t,e) -> ArrayUp(subst_tid_array subs arr, t,
                                subst_tid_expr subs e)
and subst_tid_addrarr (subs:tid_subst_t) (expr:addrarr) : addrarr =
  match expr with
    VarAddrArray v       -> VarAddrArray (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(subst_tid_addrarr subs arr,
                                        subst_tid_int subs i,
                                        subst_tid_addr subs a)
  | CellArr c            -> CellArr(subst_tid_cell subs c)
and subst_tid_tidarr (subs:tid_subst_t) (expr:tidarr) : tidarr =
  match expr with
    VarTidArray v       -> VarTidArray (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | TidArrayUp(arr,i,t) -> TidArrayUp(subst_tid_tidarr subs arr,
                                      subst_tid_int subs i,
                                      subst_tid_th subs t)
  | CellTids c            -> CellTids (subst_tid_cell subs c)
and subst_tid_set (subs:tid_subst_t) (e:set) : set =
  match e with
    VarSet v            -> VarSet (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | EmptySet            -> EmptySet
  | Singl(addr)         -> Singl(subst_tid_addr subs addr)
  | Union(s1,s2)        -> Union(subst_tid_set subs s1, subst_tid_set subs s2)
  | Intr(s1,s2)         -> Intr(subst_tid_set subs s1, subst_tid_set subs s2)
  | Setdiff(s1,s2)      -> Setdiff(subst_tid_set subs s1,
                                   subst_tid_set subs s2)
  | PathToSet(path)     -> PathToSet(subst_tid_path subs path)
  | AddrToSet(mem,addr) -> AddrToSet(subst_tid_mem subs mem,
                                     subst_tid_addr subs addr)
  | AddrToSetAt(mem,a,l)-> AddrToSetAt(subst_tid_mem subs mem,
                                       subst_tid_addr subs a,
                                       subst_tid_int subs l)
  | SetArrayRd(arr,t)   -> SetArrayRd(subst_tid_array subs arr, t)
and subst_tid_addr (subs:tid_subst_t) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | Null                      -> Null
  | Next(cell)                -> Next(subst_tid_cell subs cell)
  | NextAt(cell,l)            -> NextAt(subst_tid_cell subs cell,
                                        subst_tid_int subs l)
  | ArrAt(cell,l)             -> ArrAt(subst_tid_cell subs cell,
                                       subst_tid_int subs l)
  | FirstLocked(mem,path)     -> FirstLocked(subst_tid_mem subs mem,
                                             subst_tid_path subs path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(subst_tid_mem subs mem,
                                               subst_tid_path subs path,
                                               subst_tid_int subs l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(subst_tid_array subs arr, t)
  | AddrArrRd(arr,i)          -> AddrArrRd(subst_tid_addrarr subs arr,
                                           subst_tid_int subs i)
and subst_tid_elem (subs:tid_subst_t) (e:elem) : elem =
  match e with
    VarElem v             -> VarElem(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | CellData(cell)        -> CellData(subst_tid_cell subs cell)
  | ElemArrayRd(arr,t)    -> ElemArrayRd(subst_tid_array subs arr, t)
  | HavocListElem         -> HavocListElem
  | HavocSkiplistElem     -> HavocSkiplistElem
  | LowestElem            -> LowestElem
  | HighestElem           -> HighestElem
and subst_tid_cell (subs:tid_subst_t) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(subst_tid_elem subs data,
                                     subst_tid_addr subs addr,
                                     subst_tid_th subs th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(subst_tid_elem subs data,
                                        List.map (subst_tid_addr subs) aa,
                                        List.map (subst_tid_th subs) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(subst_tid_elem subs data,
                                       subst_tid_addrarr subs aa,
                                       subst_tid_tidarr subs ta,
                                       subst_tid_int subs l)
  | CellLock(cell,t)       -> CellLock(subst_tid_cell subs cell,
                                       subst_tid_th subs t)
  | CellLockAt(cell,l,t)   -> CellLockAt(subst_tid_cell subs cell,
                                         subst_tid_int subs l,
                                         subst_tid_th subs t)
  | CellUnlock(cell)       -> CellUnlock(subst_tid_cell subs cell)
  | CellUnlockAt(cell,l)   -> CellUnlockAt(subst_tid_cell subs cell,
                                           subst_tid_int subs l)
  | CellAt(mem,addr)       -> CellAt(subst_tid_mem subs mem,
                                     subst_tid_addr subs addr)
  | CellArrayRd(arr,t)     -> CellArrayRd(subst_tid_array subs arr, t)
  | UpdCellAddr(c,i,a)     -> UpdCellAddr(subst_tid_cell subs c,
                                          subst_tid_int subs i,
                                          subst_tid_addr subs a)
and subst_tid_setth (subs:tid_subst_t) (s:setth) : setth =
  match s with
    VarSetTh v             -> VarSetTh(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | EmptySetTh             -> EmptySetTh
  | SinglTh(th)            -> SinglTh(subst_tid_th subs th)
  | UnionTh(s1,s2)         -> UnionTh(subst_tid_setth subs s1,
                                      subst_tid_setth subs s2)
  | IntrTh(s1,s2)          -> IntrTh(subst_tid_setth subs s1,
                                     subst_tid_setth subs s2)
  | SetdiffTh(s1,s2)       -> SetdiffTh(subst_tid_setth subs s1,
                                        subst_tid_setth subs s2)
  | SetThArrayRd(arr,t)    -> SetThArrayRd(subst_tid_array subs arr, t)
and subst_tid_setint (subs:tid_subst_t) (s:setint) : setint =
  match s with
    VarSetInt v             -> VarSetInt(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | EmptySetInt             -> EmptySetInt
  | SinglInt(i)             -> SinglInt(subst_tid_int subs i)
  | UnionInt(s1,s2)         -> UnionInt(subst_tid_setint subs s1,
                                        subst_tid_setint subs s2)
  | IntrInt(s1,s2)          -> IntrInt(subst_tid_setint subs s1,
                                       subst_tid_setint subs s2)
  | SetdiffInt(s1,s2)       -> SetdiffInt(subst_tid_setint subs s1,
                                          subst_tid_setint subs s2)
  | SetIntArrayRd(arr,t)    -> SetIntArrayRd(subst_tid_array subs arr, t)
and subst_tid_setelem (subs:tid_subst_t) (s:setelem) : setelem =
  match s with
    VarSetElem v             -> VarSetElem(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | EmptySetElem             -> EmptySetElem
  | SinglElem(e)             -> SinglElem(subst_tid_elem subs e)
  | UnionElem(s1,s2)         -> UnionElem(subst_tid_setelem subs s1,
                                          subst_tid_setelem subs s2)
  | IntrElem(s1,s2)          -> IntrElem(subst_tid_setelem subs s1,
                                         subst_tid_setelem subs s2)
  | SetdiffElem(s1,s2)       -> SetdiffElem(subst_tid_setelem subs s1,
                                            subst_tid_setelem subs s2)
  | SetToElems(s,m)          -> SetToElems(subst_tid_set subs s,
                                           subst_tid_mem subs m)
  | SetElemArrayRd(arr,t)    -> SetElemArrayRd(subst_tid_array subs arr, t)
and subst_tid_path (subs:tid_subst_t) (p:path) : path =
  match p with
    VarPath v                        -> VarPath(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | Epsilon                          -> Epsilon
  | SimplePath(addr)                 -> SimplePath(subst_tid_addr subs addr)
  | GetPath(mem,add_from,add_to)     -> GetPath(subst_tid_mem subs mem,
                                                subst_tid_addr subs add_from,
                                                subst_tid_addr subs add_to)
  | GetPathAt(mem,add_from,add_to,l) -> GetPathAt(subst_tid_mem subs mem,
                                                  subst_tid_addr subs add_from,
                                                  subst_tid_addr subs add_to,
                                                  subst_tid_int subs l)
  | PathArrayRd(arr,t)           -> PathArrayRd(subst_tid_array subs arr, t)
and subst_tid_mem (subs:tid_subst_t) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | Update(mem,add,cell) -> Update(subst_tid_mem subs mem,
                                   subst_tid_addr subs add,
                                   subst_tid_cell subs cell)
  | MemArrayRd(arr,t)   -> MemArrayRd(subst_tid_array subs arr, t)
and subst_tid_int (subs:tid_subst_t) (i:integer) : integer =
  match i with
    IntVal(i)         -> IntVal(i)
  | VarInt v          -> VarInt(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | IntNeg(i)         -> IntNeg(subst_tid_int subs i)
  | IntAdd(i1,i2)     -> IntAdd(subst_tid_int subs i1, subst_tid_int subs i2)
  | IntSub(i1,i2)     -> IntSub(subst_tid_int subs i1, subst_tid_int subs i2)
  | IntMul(i1,i2)     -> IntMul(subst_tid_int subs i1, subst_tid_int subs i2)
  | IntDiv(i1,i2)     -> IntDiv(subst_tid_int subs i1, subst_tid_int subs i2)
  | IntArrayRd(arr,t) -> IntArrayRd(subst_tid_array subs arr, t)
  | IntSetMin(s)      -> IntSetMin(subst_tid_setint subs s)
  | IntSetMax(s)      -> IntSetMax(subst_tid_setint subs s)
  | CellMax(c)        -> CellMax(subst_tid_cell subs c)
  | HavocLevel        -> HavocLevel
and subst_tid_th (subs:tid_subst_t) (t:tid) : tid =
  try
    List.assoc t subs
  with _ -> begin
              match t with
              | VarTh _ -> t
              | NoTid -> t
              | CellLockId c -> CellLockId (subst_tid_cell subs c)
              | CellLockIdAt (c,l) -> CellLockIdAt (subst_tid_cell subs c,
                                                    subst_tid_int subs l)
              | TidArrayRd (a,p) -> TidArrayRd (subst_tid_array subs a,
                                                  subst_tid_th subs p)
              | TidArrRd (a,i) -> TidArrRd (subst_tid_tidarr subs a,
                                              subst_tid_int subs i)
  end
and subst_tid_atom (subs:tid_subst_t) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                 -> Append(subst_tid_path subs p1,
                                                 subst_tid_path subs p2,
                                                 subst_tid_path subs pres)
  | Reach(h,add_from,add_to,p)         -> Reach(subst_tid_mem subs h,
                                                subst_tid_addr subs add_from,
                                                subst_tid_addr subs add_to,
                                                subst_tid_path subs p)
  | ReachAt(h,a_from,a_to,l,p)         -> ReachAt(subst_tid_mem subs h,
                                                  subst_tid_addr subs a_from,
                                                  subst_tid_addr subs a_to,
                                                  subst_tid_int subs l,
                                                  subst_tid_path subs p)
  | OrderList(h,a_from,a_to)           -> OrderList(subst_tid_mem subs h,
                                                    subst_tid_addr subs a_from,
                                                    subst_tid_addr subs a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Skiplist(subst_tid_mem subs h,
                                                   subst_tid_set subs s,
                                                   subst_tid_int subs l,
                                                   subst_tid_addr subs a_from,
                                                   subst_tid_addr subs a_to,
                                                   subst_tid_setelem subs elems)
  | In(a,s)                            -> In(subst_tid_addr subs a,
                                             subst_tid_set subs s)
  | SubsetEq(s_in,s_out)               -> SubsetEq(subst_tid_set subs s_in,
                                                   subst_tid_set subs s_out)
  | InTh(th,s)                         -> InTh(subst_tid_th subs th,
                                               subst_tid_setth subs s)
  | SubsetEqTh(s_in,s_out)             -> SubsetEqTh(subst_tid_setth subs s_in,
                                                     subst_tid_setth subs s_out)
  | InInt(i,s)                         -> InInt(subst_tid_int subs i,
                                                subst_tid_setint subs s)
  | SubsetEqInt(s_in,s_out)            -> SubsetEqInt(subst_tid_setint subs s_in,
                                                      subst_tid_setint subs s_out)
  | InElem(e,s)                        -> InElem(subst_tid_elem subs e,
                                                 subst_tid_setelem subs s)
  | SubsetEqElem(s_in,s_out)           -> SubsetEqElem(subst_tid_setelem subs s_in,
                                                       subst_tid_setelem subs s_out)
  | Less(i1,i2)                        -> Less(subst_tid_int subs i1,
                                               subst_tid_int subs i2)
  | Greater(i1,i2)                     -> Greater(subst_tid_int subs i1,
                                                  subst_tid_int subs i2)
  | LessEq(i1,i2)                      -> LessEq(subst_tid_int subs i1,
                                                 subst_tid_int subs i2)
  | GreaterEq(i1,i2)                   -> GreaterEq(subst_tid_int subs i1,
                                                    subst_tid_int subs i2)
  | LessTid(t1,t2)                     -> LessTid(subst_tid_th subs t1,
                                                  subst_tid_th subs t2)
  | LessElem(e1,e2)                    -> LessElem(subst_tid_elem subs e1,
                                                   subst_tid_elem subs e2)
  | GreaterElem(e1,e2)                 -> GreaterElem(subst_tid_elem subs e1,
                                                      subst_tid_elem subs e2)
  | Eq(exp)                            -> Eq(subst_tid_eq subs exp)
  | InEq(exp)                          -> InEq(subst_tid_ineq subs exp)
  | BoolVar v                          -> BoolVar(V.set_param v (subst_shared_or_local subs (V.parameter v)))
  | BoolArrayRd(arr,t)                 -> BoolArrayRd(subst_tid_array subs arr, t)
  | PC (pc,t,primed)                   -> PC (pc, subst_shared_or_local subs t,primed)
  | PCUpdate (pc,t)                    -> PCUpdate (pc, subst_tid_th subs t)
  | PCRange (pc1,pc2,t,primed)         -> PCRange (pc1, pc2, subst_shared_or_local subs t, primed)

(*
and subst_tid_literal (subs:tid_subst_t) (l:literal) : literal =
  match l with
    Atom a    -> Atom (subst_tid_atom subs a)
  | NegAtom a -> NegAtom (subst_tid_atom subs a)
*)
and subst_tid_eq (subs:tid_subst_t) ((t1,t2):eq) : eq =
  (subst_tid_term subs t1, subst_tid_term subs t2)

and subst_tid_ineq (subs:tid_subst_t) ((t1,t2):diseq) : diseq =
  (subst_tid_term subs t1, subst_tid_term subs t2)

and subst_tid_fs () = Formula.make_trans
                        Formula.GenericLiteralTrans
                        (fun info a -> subst_tid_atom info a)

and subst_tid (subs:tid_subst_t) (phi:formula) : formula =
  Formula.formula_trans (subst_tid_fs()) subs phi
(*
and subst_tid_conjunctive_formula (subs:tid_subst_t)
                                  (cf:conjunctive_formula)
                                    : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (subst_tid_literal subs) ls)
and subst_tid (subs:tid_subst_t) (phi:formula) : formula =
  match phi with
    Literal(lit)   -> Literal(subst_tid_literal subs lit)
  | True           -> True
  | False          -> False
  | And(f1,f2)     -> And(subst_tid subs f1, subst_tid subs f2)
  | Or(f1,f2)      -> Or(subst_tid subs f1, subst_tid subs f2)
  | Not(f)         -> Not(subst_tid subs f)
  | Implies(f1,f2) -> Implies(subst_tid subs f1, subst_tid subs f2)
  | Iff (f1,f2)    -> Iff(subst_tid subs f1, subst_tid subs f2)
*)

let subst_to_str (sub:tid_subst_t) : string =
  "{" ^ (String.concat ", " $
         List.map (fun (i,j) -> (tid_to_str j)^"<-"^(tid_to_str i)) sub) ^ "}"


let subst_full_domain_assign (tid_list:tid list) (subst:tid_subst_t) : bool =
  let dom = subst_domain subst
  in
    List.for_all (fun t -> ThreadSet.mem t dom) tid_list


let subst_full_codomain_assign (tid_list:tid list) (subst:tid_subst_t) : bool =
  let codom = subst_codomain subst
  in
    List.for_all (fun t -> ThreadSet.mem t codom) tid_list


let is_id_subst (subst:tid_subst_t) : bool =
  List.for_all (fun (i,j) -> i = j) subst



(* VARIABLE SUBSTITUTION FUNCTIONS *)

let rec subst_vars_term (subs:V.subst_t) (expr:term) : term =
  match expr with
    VarT v              -> VarT (V.subst subs v)
  | SetT(set)           -> SetT(subst_vars_set subs set)
  | AddrT(addr)         -> AddrT(subst_vars_addr subs addr)
  | ElemT(elem)         -> ElemT(subst_vars_elem subs elem)
  | TidT(th)           -> TidT(subst_vars_th subs th)
  | CellT(cell)         -> CellT(subst_vars_cell subs cell)
  | SetThT(setth)       -> SetThT(subst_vars_setth subs setth)
  | SetIntT(setint)     -> SetIntT(subst_vars_setint subs setint)
  | SetElemT(setelem)   -> SetElemT(subst_vars_setelem subs setelem)
  | PathT(path)         -> PathT(subst_vars_path subs path)
  | MemT(mem)           -> MemT(subst_vars_mem subs mem)
  | IntT(i)             -> IntT(subst_vars_int subs i)
  | ArrayT(arr)         -> ArrayT(subst_vars_array subs arr)
  | AddrArrayT(arr)     -> AddrArrayT(subst_vars_addrarr subs arr)
  | TidArrayT(arr)      -> TidArrayT(subst_vars_tidarr subs arr)


and subst_vars_expr (subs:V.subst_t) (expr:expr_t) : expr_t =
  match expr with
    Term t    -> Term (subst_vars_term subs t)
  | Formula b -> Formula (subst_vars subs b)


and subst_vars_array (subs:V.subst_t) (expr:arrays) : arrays =
  match expr with
    VarArray v       -> VarArray (V.subst subs v)
  | ArrayUp(arr,t,e) -> ArrayUp(subst_vars_array subs arr, t,
                                subst_vars_expr subs e)


and subst_vars_addrarr (subs:V.subst_t) (expr:addrarr) : addrarr =
  match expr with
    VarAddrArray v       -> VarAddrArray (V.subst subs v)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(subst_vars_addrarr subs arr,
                                        subst_vars_int subs i,
                                        subst_vars_addr subs a)
  | CellArr c            -> CellArr(subst_vars_cell subs c)


and subst_vars_tidarr (subs:V.subst_t) (expr:tidarr) : tidarr =
  match expr with
    VarTidArray v       -> VarTidArray (V.subst subs v)
  | TidArrayUp(arr,i,t) -> TidArrayUp(subst_vars_tidarr subs arr,
                                      subst_vars_int subs i,
                                      subst_vars_th subs t)
  | CellTids c            -> CellTids (subst_vars_cell subs c)


and subst_vars_set (subs:V.subst_t) (e:set) : set =
  match e with
    VarSet v            -> VarSet (V.subst subs v)
  | EmptySet            -> EmptySet
  | Singl(addr)         -> Singl(subst_vars_addr subs addr)
  | Union(s1,s2)        -> Union(subst_vars_set subs s1, subst_vars_set subs s2)
  | Intr(s1,s2)         -> Intr(subst_vars_set subs s1, subst_vars_set subs s2)
  | Setdiff(s1,s2)      -> Setdiff(subst_vars_set subs s1,
                                   subst_vars_set subs s2)
  | PathToSet(path)     -> PathToSet(subst_vars_path subs path)
  | AddrToSet(mem,addr) -> AddrToSet(subst_vars_mem subs mem,
                                     subst_vars_addr subs addr)
  | AddrToSetAt(mem,a,l)-> AddrToSetAt(subst_vars_mem subs mem,
                                       subst_vars_addr subs a,
                                       subst_vars_int subs l)
  | SetArrayRd(arr,t)   -> SetArrayRd(subst_vars_array subs arr, t)


and subst_vars_addr (subs:V.subst_t) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr(V.subst subs v)
  | Null                      -> Null
  | Next(cell)                -> Next(subst_vars_cell subs cell)
  | NextAt(cell,l)            -> NextAt(subst_vars_cell subs cell,
                                        subst_vars_int subs l)
  | ArrAt(cell,l)             -> ArrAt(subst_vars_cell subs cell,
                                       subst_vars_int subs l)
  | FirstLocked(mem,path)     -> FirstLocked(subst_vars_mem subs mem,
                                             subst_vars_path subs path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(subst_vars_mem subs mem,
                                               subst_vars_path subs path,
                                               subst_vars_int subs l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(subst_vars_array subs arr, t)
  | AddrArrRd(arr,i)          -> AddrArrRd(subst_vars_addrarr subs arr,
                                           subst_vars_int subs i)


and subst_vars_elem (subs:V.subst_t) (e:elem) : elem =
  match e with
    VarElem v             -> VarElem(V.subst subs v)
  | CellData(cell)        -> CellData(subst_vars_cell subs cell)
  | ElemArrayRd(arr,t)    -> ElemArrayRd(subst_vars_array subs arr, t)
  | HavocListElem         -> HavocListElem
  | HavocSkiplistElem     -> HavocSkiplistElem
  | LowestElem            -> LowestElem
  | HighestElem           -> HighestElem


and subst_vars_cell (subs:V.subst_t) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (V.subst subs v)
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(subst_vars_elem subs data,
                                     subst_vars_addr subs addr,
                                     subst_vars_th subs th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(subst_vars_elem subs data,
                                        List.map (subst_vars_addr subs) aa,
                                        List.map (subst_vars_th subs) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(subst_vars_elem subs data,
                                       subst_vars_addrarr subs aa,
                                       subst_vars_tidarr subs ta,
                                       subst_vars_int subs l)
  | CellLock(cell,t)       -> CellLock(subst_vars_cell subs cell,
                                       subst_vars_th subs t)
  | CellLockAt(cell,l,t)   -> CellLockAt(subst_vars_cell subs cell,
                                         subst_vars_int subs l,
                                         subst_vars_th subs t)
  | CellUnlock(cell)       -> CellUnlock(subst_vars_cell subs cell)
  | CellUnlockAt(cell,l)   -> CellUnlockAt(subst_vars_cell subs cell,
                                           subst_vars_int subs l)
  | CellAt(mem,addr)       -> CellAt(subst_vars_mem subs mem,
                                     subst_vars_addr subs addr)
  | CellArrayRd(arr,t)     -> CellArrayRd(subst_vars_array subs arr, t)
  | UpdCellAddr(c,i,a)     -> UpdCellAddr(subst_vars_cell subs c,
                                          subst_vars_int subs i,
                                          subst_vars_addr subs a)


and subst_vars_setth (subs:V.subst_t) (s:setth) : setth =
  match s with
    VarSetTh v             -> VarSetTh(V.subst subs v)
  | EmptySetTh             -> EmptySetTh
  | SinglTh(th)            -> SinglTh(subst_vars_th subs th)
  | UnionTh(s1,s2)         -> UnionTh(subst_vars_setth subs s1,
                                      subst_vars_setth subs s2)
  | IntrTh(s1,s2)          -> IntrTh(subst_vars_setth subs s1,
                                     subst_vars_setth subs s2)
  | SetdiffTh(s1,s2)       -> SetdiffTh(subst_vars_setth subs s1,
                                        subst_vars_setth subs s2)
  | SetThArrayRd(arr,t)    -> SetThArrayRd(subst_vars_array subs arr, t)


and subst_vars_setint (subs:V.subst_t) (s:setint) : setint =
  match s with
    VarSetInt v             -> VarSetInt(V.subst subs v)
  | EmptySetInt             -> EmptySetInt
  | SinglInt(i)             -> SinglInt(subst_vars_int subs i)
  | UnionInt(s1,s2)         -> UnionInt(subst_vars_setint subs s1,
                                        subst_vars_setint subs s2)
  | IntrInt(s1,s2)          -> IntrInt(subst_vars_setint subs s1,
                                       subst_vars_setint subs s2)
  | SetdiffInt(s1,s2)       -> SetdiffInt(subst_vars_setint subs s1,
                                          subst_vars_setint subs s2)
  | SetIntArrayRd(arr,t)    -> SetIntArrayRd(subst_vars_array subs arr, t)


and subst_vars_setelem (subs:V.subst_t) (s:setelem) : setelem =
  match s with
    VarSetElem v             -> VarSetElem(V.subst subs v)
  | EmptySetElem             -> EmptySetElem
  | SinglElem(e)             -> SinglElem(subst_vars_elem subs e)
  | UnionElem(s1,s2)         -> UnionElem(subst_vars_setelem subs s1,
                                          subst_vars_setelem subs s2)
  | IntrElem(s1,s2)          -> IntrElem(subst_vars_setelem subs s1,
                                         subst_vars_setelem subs s2)
  | SetdiffElem(s1,s2)       -> SetdiffElem(subst_vars_setelem subs s1,
                                            subst_vars_setelem subs s2)
  | SetToElems(s,m)          -> SetToElems(subst_vars_set subs s,
                                           subst_vars_mem subs m)
  | SetElemArrayRd(arr,t)    -> SetElemArrayRd(subst_vars_array subs arr, t)


and subst_vars_path (subs:V.subst_t) (p:path) : path =
  match p with
    VarPath v                        -> VarPath(V.subst subs v)
  | Epsilon                          -> Epsilon
  | SimplePath(addr)                 -> SimplePath(subst_vars_addr subs addr)
  | GetPath(mem,add_from,add_to)     -> GetPath(subst_vars_mem subs mem,
                                                subst_vars_addr subs add_from,
                                                subst_vars_addr subs add_to)
  | GetPathAt(mem,add_from,add_to,l) -> GetPathAt(subst_vars_mem subs mem,
                                                  subst_vars_addr subs add_from,
                                                  subst_vars_addr subs add_to,
                                                  subst_vars_int subs l)
  | PathArrayRd(arr,t)           -> PathArrayRd(subst_vars_array subs arr, t)


and subst_vars_mem (subs:V.subst_t) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem(V.subst subs v)
  | Update(mem,add,cell) -> Update(subst_vars_mem subs mem,
                                   subst_vars_addr subs add,
                                   subst_vars_cell subs cell)
  | MemArrayRd(arr,t)   -> MemArrayRd(subst_vars_array subs arr, t)


and subst_vars_int (subs:V.subst_t) (i:integer) : integer =
  match i with
    IntVal(i)         -> IntVal(i)
  | VarInt v          -> VarInt(V.subst subs v)
  | IntNeg(i)         -> IntNeg(subst_vars_int subs i)
  | IntAdd(i1,i2)     -> IntAdd(subst_vars_int subs i1, subst_vars_int subs i2)
  | IntSub(i1,i2)     -> IntSub(subst_vars_int subs i1, subst_vars_int subs i2)
  | IntMul(i1,i2)     -> IntMul(subst_vars_int subs i1, subst_vars_int subs i2)
  | IntDiv(i1,i2)     -> IntDiv(subst_vars_int subs i1, subst_vars_int subs i2)
  | IntArrayRd(arr,t) -> IntArrayRd(subst_vars_array subs arr, t)
  | IntSetMin(s)      -> IntSetMin(subst_vars_setint subs s)
  | IntSetMax(s)      -> IntSetMax(subst_vars_setint subs s)
  | CellMax(c)        -> CellMax(subst_vars_cell subs c)
  | HavocLevel        -> HavocLevel


and subst_vars_th (subs:V.subst_t) (t:tid) : tid =
  match t with
  | VarTh v -> VarTh (V.subst subs v)
  | NoTid -> NoTid
  | CellLockId c -> CellLockId (subst_vars_cell subs c)
  | CellLockIdAt (c,l) -> CellLockIdAt (subst_vars_cell subs c,
                                        subst_vars_int subs l)
  | TidArrayRd (a,p) -> TidArrayRd (subst_vars_array subs a,
                                      subst_vars_th subs p)
  | TidArrRd (a,i) -> TidArrRd (subst_vars_tidarr subs a,
                                  subst_vars_int subs i)


and subst_vars_atom (subs:V.subst_t) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                 -> Append(subst_vars_path subs p1,
                                                 subst_vars_path subs p2,
                                                 subst_vars_path subs pres)
  | Reach(h,add_from,add_to,p)         -> Reach(subst_vars_mem subs h,
                                                subst_vars_addr subs add_from,
                                                subst_vars_addr subs add_to,
                                                subst_vars_path subs p)
  | ReachAt(h,a_from,a_to,l,p)         -> ReachAt(subst_vars_mem subs h,
                                                  subst_vars_addr subs a_from,
                                                  subst_vars_addr subs a_to,
                                                  subst_vars_int subs l,
                                                  subst_vars_path subs p)
  | OrderList(h,a_from,a_to)           -> OrderList(subst_vars_mem subs h,
                                                    subst_vars_addr subs a_from,
                                                    subst_vars_addr subs a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Skiplist(subst_vars_mem subs h,
                                                   subst_vars_set subs s,
                                                   subst_vars_int subs l,
                                                   subst_vars_addr subs a_from,
                                                   subst_vars_addr subs a_to,
                                                   subst_vars_setelem subs elems)
  | In(a,s)                            -> In(subst_vars_addr subs a,
                                             subst_vars_set subs s)
  | SubsetEq(s_in,s_out)               -> SubsetEq(subst_vars_set subs s_in,
                                                   subst_vars_set subs s_out)
  | InTh(th,s)                         -> InTh(subst_vars_th subs th,
                                               subst_vars_setth subs s)
  | SubsetEqTh(s_in,s_out)             -> SubsetEqTh(subst_vars_setth subs s_in,
                                                     subst_vars_setth subs s_out)
  | InInt(i,s)                         -> InInt(subst_vars_int subs i,
                                                subst_vars_setint subs s)
  | SubsetEqInt(s_in,s_out)            -> SubsetEqInt(subst_vars_setint subs s_in,
                                                      subst_vars_setint subs s_out)
  | InElem(e,s)                        -> InElem(subst_vars_elem subs e,
                                                 subst_vars_setelem subs s)
  | SubsetEqElem(s_in,s_out)           -> SubsetEqElem(subst_vars_setelem subs s_in,
                                                       subst_vars_setelem subs s_out)
  | Less(i1,i2)                        -> Less(subst_vars_int subs i1,
                                               subst_vars_int subs i2)
  | Greater(i1,i2)                     -> Greater(subst_vars_int subs i1,
                                                  subst_vars_int subs i2)
  | LessEq(i1,i2)                      -> LessEq(subst_vars_int subs i1,
                                                 subst_vars_int subs i2)
  | GreaterEq(i1,i2)                   -> GreaterEq(subst_vars_int subs i1,
                                                    subst_vars_int subs i2)
  | LessTid(t1,t2)                     -> LessTid(subst_vars_th subs t1,
                                                  subst_vars_th subs t2)
  | LessElem(e1,e2)                    -> LessElem(subst_vars_elem subs e1,
                                                   subst_vars_elem subs e2)
  | GreaterElem(e1,e2)                 -> GreaterElem(subst_vars_elem subs e1,
                                                      subst_vars_elem subs e2)
  | Eq(exp)                            -> Eq(subst_vars_eq subs exp)
  | InEq(exp)                          -> InEq(subst_vars_ineq subs exp)
  | BoolVar v                          -> BoolVar(V.set_param v (V.subst_shared_or_local subs (V.parameter v)))
  | BoolArrayRd(arr,t)                 -> BoolArrayRd(subst_vars_array subs arr, t)
  | PC (pc,t,primed)                   -> PC (pc, V.subst_shared_or_local subs t, primed)
  | PCUpdate (pc,t)                    -> PCUpdate (pc, subst_vars_th subs t)
  | PCRange (pc1,pc2,t,primed)         -> PCRange (pc1, pc2, V.subst_shared_or_local subs t, primed)



(*
and subst_vars_literal (subs:V.subst_t) (l:literal) : literal =
  match l with
    Atom a    -> Atom (subst_vars_atom subs a)
  | NegAtom a -> NegAtom (subst_vars_atom subs a)
*)


and subst_vars_eq (subs:V.subst_t) ((t1,t2):eq) : eq =
  (subst_vars_term subs t1, subst_vars_term subs t2)


and subst_vars_ineq (subs:V.subst_t) ((t1,t2):diseq) : diseq =
  (subst_vars_term subs t1, subst_vars_term subs t2)


and subst_vars_fs () = Formula.make_trans
                         Formula.GenericLiteralTrans
                         (fun info a -> subst_vars_atom info a)


and subst_vars (subs:V.subst_t) (phi:formula) : formula =
  Formula.formula_trans (subst_vars_fs()) subs phi
(*
and subst_vars_conjunctive_formula (subs:V.subst_t)
                                   (cf:conjunctive_formula)
                                    : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (subst_vars_literal subs) ls)


and subst_vars (subs:V.subst_t) (phi:formula) : formula =
  match phi with
    Literal(lit)   -> Literal(subst_vars_literal subs lit)
  | True           -> True
  | False          -> False
  | And(f1,f2)     -> And(subst_vars subs f1, subst_vars subs f2)
  | Or(f1,f2)      -> Or(subst_vars subs f1, subst_vars subs f2)
  | Not(f)         -> Not(subst_vars subs f)
  | Implies(f1,f2) -> Implies(subst_vars subs f1, subst_vars subs f2)
  | Iff (f1,f2)    -> Iff(subst_vars subs f1, subst_vars subs f2)
*)


(* FORMULA MANIPULATION FUNCTIONS *)



(* Converts an expression to a format understandable by Sriram's tool "trs" *)
let rec to_trs (expr:formula) : formula =
  let add_one i = IntAdd (i, IntVal 1) in
  let tid_to_int t = match t with
                       VarTh v -> VarInt v
                     | _ -> let msg = "Tid to int conversion in to_trs" in
                              raise(Not_implemented msg) in
  let rec conv e neg =
    (* First argument in formula, second tells if it must be negated *)
    match (e,neg) with
      (F.True, false)   -> F.True
    | (F.True, true)    -> F.False
    | (F.False, false)  -> F.False
    | (F.False, true)   -> F.True
    | (F.Literal (F.NegAtom a), false) -> conv (F.Literal (F.Atom a)) true
    | (F.Literal (F.NegAtom a), true ) -> conv (F.Literal (F.Atom a)) false
    | (F.Literal (F.Atom (Less (n,m))),            false) -> lesseq_form (add_one n) m
    | (F.Literal (F.Atom (Less (n,m))),            true ) -> greatereq_form n m
    | (F.Literal (F.Atom (Greater (n,m))),         false) -> greatereq_form n (add_one m)
    | (F.Literal (F.Atom (Greater (n,m))),         true ) -> lesseq_form n m
    | (F.Literal (F.Atom (LessEq (n,m))),          false) -> lesseq_form n m
    | (F.Literal (F.Atom (LessEq (n,m))),          true ) -> greatereq_form n (add_one m)
    | (F.Literal (F.Atom (GreaterEq (n,m))),       false) -> greatereq_form n m
    | (F.Literal (F.Atom (GreaterEq (n,m))),       true ) -> lesseq_form (add_one n) m
    | (F.Literal (F.Atom (Eq (IntT n, IntT m))),   false) -> eq_int n m
    | (F.Literal (F.Atom (Eq (IntT n, IntT m))),   true ) -> F.Or (lesseq_form (add_one n) m,
                                                                   greatereq_form n (add_one m))
    | (F.Literal (F.Atom (InEq (IntT n, IntT m))), false) -> F.Or (lesseq_form (add_one n) m,
                                                                   greatereq_form n (add_one m))
    | (F.Literal (F.Atom (InEq (IntT n, IntT m))), true ) -> eq_int n m
    | (F.Literal (F.Atom (LessTid (s,t))),         false) -> lesseq_form (add_one (tid_to_int s)) (tid_to_int t)
    | (F.Literal (F.Atom (LessTid (s,t))),         true ) -> greatereq_form (tid_to_int s) (tid_to_int t)
    | (F.And (e1, e2),     false) -> F.And (conv e1 false, conv e2 false)
    | (F.And (e1, e2),     true ) -> F.Or (conv e1 true, conv e2 true)
    | (F.Or (e1, e2),      false) -> F.Or (conv e1 false, conv e2 false)
    | (F.Or (e1, e2),      true ) -> F.And (conv e1 true, conv e2 true)
    | (F.Not e,            false) -> conv e true
    | (F.Not e,            true ) -> conv e false
    | (F.Implies (e1, e2), false) -> F.Or (conv e1 true, conv e2 false)
    | (F.Implies (e1, e2), true ) -> F.And (conv e1 false, conv e2 true)
    | (F.Iff (e1, e2),     false) -> F.And (F.Or (conv e1 true, conv e2 false),
                                        F.Or (conv e1 false, conv e2 true))
    | (F.Iff (e1, e2),     true ) -> F.Or (F.And (conv e1 false, conv e2 true),
                                      F.And (conv e1 true, conv e2 false))
    | (e,                false) -> e
    | (e,                true ) -> F.Not e
  in
    conv expr false

 


(* INITIAL ASSIGNMENT FUNCTION *)
let assign_var (v:V.t) (init:initVal_t option) : formula list =
  match init with
  | Some (Equality t)  -> [eq_term (var_to_term v) t]
  | Some (Condition c) -> [c]
  | None               -> []


(* EXPRESSION PRESERVATION FUNCTIONS *)
let pres_th_param (t:term) (new_th:V.shared_or_local) : V.shared_or_local =
  match term_scope t with
  | V.GlobalScope -> V.Shared
  | V.Scope _ -> new_th


let construct_term_eq (v:term)
                      (th_p:V.shared_or_local)
                      (e:expr_t) : (term list * formula) =
(*  let new_th = pres_th_param v th_p in *)

  match (v,e) with
    (* Variables *)
    (VarT var, Formula t) ->
      (* Possibly I have to inject the Bool sort to the variable *)
      let modif     = [VarT (var_base_info var)] in
      let new_th    = pres_th_param v th_p in
      let left_atom = prime_atom (BoolVar (V.set_param var new_th)) in
      let param_t   = param th_p t
      in
        (modif, F.Iff (F.Literal (F.Atom left_atom), param_t))

  | (VarT var, Term t) ->
      let modif     = [VarT (var_base_info var)] in
      let new_th    = pres_th_param v th_p in
      let left_term = prime_term $ param_term new_th v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Sets of addresses *)
  | (SetT (VarSet var), Term t) ->
      let modif     = [SetT(VarSet(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Sets of integers *)
  | (SetIntT (VarSetInt var), Term t) ->
      let modif     = [SetIntT(VarSetInt(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Sets of elements *)
  | (SetElemT (VarSetElem var), Term t) ->
      let modif     = [SetElemT(VarSetElem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Sets of threads *)
  | (SetThT (VarSetTh var), Term t) ->
      let modif     = [SetThT(VarSetTh(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Elements *)
  | (ElemT (VarElem var), Term t) ->
      let modif     = [ElemT(VarElem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (ElemT (CellData (VarCell var)), Term t) ->
      let modif     = [ElemT(CellData(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Threads *)
  | (TidT (VarTh var), Term t) ->
      let modif     = [TidT(VarTh(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (TidT (CellLockId (VarCell var)), Term t) ->
      let modif     = [TidT (CellLockId(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (TidT (CellLockIdAt (VarCell var, i)), Term t) ->
      let modif     = [TidT (CellLockIdAt(VarCell(var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (TidT (TidArrRd (CellTids (VarCell var), i)), Term t) ->
      let modif     = [TidT (TidArrRd (CellTids(VarCell(var_base_info var)),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (TidT (TidArrRd (VarTidArray var,i)), Term t) ->
      let modif     = [TidT(TidArrRd(VarTidArray (var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Addresses *)
  | (AddrT (VarAddr var), Term t) ->
      let modif     = [AddrT(VarAddr(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (AddrT (Next (VarCell var)), Term t) ->
      let modif     = [AddrT(Next(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (AddrT (ArrAt (VarCell var, i)), Term t) ->
      let modif     = [AddrT(ArrAt(VarCell(var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (AddrT (AddrArrRd (CellArr (VarCell var), i)), Term t) ->
      let modif     = [AddrT(AddrArrRd(CellArr(VarCell(var_base_info var)),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  | (AddrT (AddrArrRd (VarAddrArray var,i)), Term t) ->
      let modif     = [AddrT(AddrArrRd(VarAddrArray (var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Cells *)
  (* TODO: Not sure if this case is ok *)
  | (CellT (VarCell var as c), Term CellT (CellLock (VarCell _, _))) ->
      let new_th    = pres_th_param v th_p in
      let modif     = [TidT(CellLockId(VarCell(var_base_info var)))] in
      let new_tid   = (match th_p with
                       | V.Shared -> NoTid
                       | V.Local t -> (VarTh t)) in
      let left_term = prime_term (CellT (VarCell
                        (V.set_param (V.unprime var) new_th))) in
      (modif, eq_term left_term (CellT(MkCell(CellData c, Next c, new_tid))))

  (* TOFIX: We are missing the case for TSLK and TSL *)

  | (CellT (VarCell var), Term t) ->
      let modif     = [CellT(VarCell(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)


  (* Paths *)
  | (PathT (VarPath var), Term t) ->
      let modif     = [PathT(VarPath(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Memories *)
  | (MemT (VarMem var), Term t) ->
      let modif     = [MemT(VarMem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Integers *)
  | (IntT (VarInt var), Term t) ->
      let modif = [IntT(VarInt(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Arrays with domain of thread identifiers *)
  | (ArrayT (VarArray var), Term t) ->
      let modif     = [ArrayT(VarArray(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, eq_term left_term param_t)

  (* Pointer support *)
  (* Missing for this cases *)
  | (_, Term t)                 ->
      Interface.Err.msg "Unexpected assignment" $
              sprintf "When constructing transition relation for \
                       assignment between term \"%s\" and \
                       expression \"%s\"." (term_to_str v)
                                           (term_to_str t);
      raise(Incompatible_assignment(v,e))

  | (_, Formula t)                ->
      Interface.Err.msg "Unexpected assignment" $
              sprintf "When construction transition relation for \
                       assignment between term \"%s\" and formula \
                       expression \"%s\"." (term_to_str v)
                                           (formula_to_str t);
      raise(Incompatible_assignment(v,e))


let construct_pres_term (t:term) (th_p:V.shared_or_local) : formula =
  match t with
    VarT var -> let bool_var = Formula (boolvar var) in
                  snd $ construct_term_eq t th_p bool_var
  | _        -> snd $ construct_term_eq t th_p (Term (param_term th_p t))



let construct_term_eq_as_array (v:term)
                               (th_p:V.shared_or_local)
                               (e:expr_t) : (term list * formula) =
  match (term_scope v, th_p) with
  | (V.Scope _, V.Local th) ->
      begin
        let arr        = array_var_from_term v false in
        let primed_arr = array_var_from_term v true in
        let new_expr   =
          let cell_arr = CellArrayRd(arr,VarTh th) in
          match (v,e) with
          | (ElemT(CellData(c)), Term (ElemT e)) ->
              Term(CellT(MkCell(param_elem th_p e,
                                Next cell_arr,
                                CellLockId cell_arr)))
          | (AddrT(Next(c)), Term (AddrT a)) ->
              Term(CellT(MkCell(CellData cell_arr,
                                param_addr th_p a,
                                CellLockId cell_arr)))
          | (CellT (VarCell _), Term (CellT(CellLock(d,_)))) ->
              let my_tid = (match th_p with
                            | V.Shared -> NoTid
                            | V.Local t -> VarTh t ) in
              let new_d  = param_cell th_p d in
                             Term(CellT(MkCell(CellData new_d,
                                               Next new_d,
                                               my_tid)))
          | (TidT(CellLockId(c)), Term (TidT tid)) ->
              Term(CellT(MkCell(CellData cell_arr,
                                Next cell_arr,
                                param_th th_p tid)))
          | _ -> param_expr th_p e in
        let modif_arr  = ArrayT(ArrayUp(arr, VarTh th, new_expr)) in
        let assign     = eq_term (ArrayT primed_arr) modif_arr in
        ([ArrayT arr], assign)
      end
  | (V.GlobalScope, _) ->
      begin
        match (v,e) with
        | (AddrT (AddrArrRd(arr,i)), Term (AddrT a)) ->
            let primed_arr = prime_addrarr arr in
            let modif_arr = AddrArrayT(AddrArrayUp(param_addrarr th_p arr,
                                                   param_int th_p i,
                                                   param_addr th_p a)) in
            let assign = eq_term (AddrArrayT (param_addrarr th_p primed_arr)) modif_arr in
            ([AddrArrayT arr], assign)
        | (TidT (TidArrRd(arr,i)), Term (TidT t)) ->
            let primed_arr = prime_tidarr arr in
            let modif_arr = TidArrayT(TidArrayUp(param_tidarr th_p arr,
                                                 param_int th_p i,
                                                 param_th th_p t)) in
            let assign = eq_term (TidArrayT (param_tidarr th_p primed_arr)) modif_arr in
            ([TidArrayT arr], assign)
        | _ -> construct_term_eq v th_p e
      end
  | _ -> Interface.Err.msg "Invalid argument" $
                 sprintf "When trying to construct a local array assignment \
                          for term \"%s\" with expression \"%s\", no thread \
                          identifier to denote the array position to be \
                          modified was provided." (term_to_str v)
                                                  (expr_to_str e);
                 raise(Invalid_argument)


(* NUMERIC EXPRESSION FUNCTIONS *)
let new_num_pos_var_id (base:string) (i:int) : V.id =
  sprintf "%s%i" base i


let new_label_pos_var_id (base:string) (lbl:string) : V.id =
  sprintf "%s%s" base lbl


let new_num_pos_var (base:string) (i:int) : integer =
  VarInt (build_var (new_num_pos_var_id base i) Int false
                    V.Shared (V.Scope ""))


let new_label_pos_var (base:string) (lbl:string) : integer =
  VarInt (build_var (new_label_pos_var_id base lbl) Int false
                    V.Shared (V.Scope ""))


(* COUNTING ABSTRACTION FUNCTIONS *)

(* FOR SRIRAM ABS-INT *)
let expr_and_removing_true (f1:formula) (f2:formula) : formula =
  if f1 = F.True then f2
  else if f2 = F.True then f1
  else F.And(f1,f2)


let countAbs_var (i:int) : V.t =
  build_global_var (Conf.defCountAbs_name ^ string_of_int i) Int


let someone_at (i:int) : formula =
  let var = new_num_pos_var Conf.defCountAbs_name i
  in
    greatereq_form var (IntVal 1)


let someone_at_labels (ls:string list) : formula =
  let loc_vars = List.map (fun l ->
                   let v = new_label_pos_var Conf.defCountAbs_name l
                   in
                     greatereq_form v (IntVal 1)
                 ) ls
  in
    Formula.conj_list loc_vars


let build_assign (v:integer) (e:integer) : formula =
  eq_int (prime_int v) e


let build_pos_change (curr:int) (next:int) : formula =
  let curr_var    = new_num_pos_var Conf.defCountAbs_name curr in
  let next_var    = new_num_pos_var Conf.defCountAbs_name next in
  let jump        = if curr = next then
                      IntVal 0
                    else
                      IntVal 1 in
  let curr_modif  = build_assign curr_var (IntSub (curr_var, jump)) in
  let next_modif  = build_assign next_var (IntAdd (next_var, jump))
  in
    expr_and_removing_true curr_modif next_modif


let build_label_change (curr:string list) (next:string list) : formula =
  let one = IntVal 1 in
  let build_label_var lbl = new_label_pos_var Conf.defCountAbs_name lbl in
  let (shared,only_curr) = List.partition (fun e -> List.mem e next) curr in
  let only_next = List.filter (fun e -> not (List.mem e shared)) next in
  let only_curr_modif = List.map (fun lbl ->
                          let var = build_label_var lbl in
                            build_assign var (IntSub (var, one))
                        ) only_curr in
  let only_next_modif = List.map (fun lbl ->
                          let var = build_label_var lbl in
                            build_assign var (IntAdd (var, one))
                        ) only_next in
  let shared_modif = List.map (fun lbl ->
                       let var = build_label_var lbl in
                         build_assign var var
                     ) shared
  in
    Formula.conj_list (only_curr_modif @ only_next_modif @ shared_modif)


let required_sorts (phi:formula) : sort list =
  let empty = SortSet.empty in
  let union = SortSet.union in
  let add = SortSet.add in
  let single = SortSet.singleton in
  let append s sets = add s (List.fold_left union empty sets) in


  let rec req_fs () = Formula.make_fold
                        Formula.GenericLiteralFold
                        (fun info a -> req_atom a)
                        (fun info -> empty)
                        (union)

  and req_f (phi:formula) : SortSet.t =
    Formula.formula_fold (req_fs()) () phi

(*
  let rec req_f (phi:formula) : SortSet.t =
    match phi with
    | Literal l       -> req_l l
    | True            -> empty
    | False           -> empty
    | And (f1,f2)     -> union (req_f f1) (req_f f2)
    | Or (f1,f2)      -> union (req_f f1) (req_f f2)
    | Not f           -> req_f f
    | Implies (f1,f2) -> union (req_f f1) (req_f f2)
    | Iff (f1,f2)     -> union (req_f f1) (req_f f2)

  and req_l (l:literal) : SortSet.t =
    match l with
    | Atom a    -> req_atom a
    | NegAtom a -> req_atom a
*)

  and req_atom (a:atom) : SortSet.t =
    match a with
    | Append (p1,p2,p3)     -> append Bool [req_p p1;req_p p2;req_p p3]
    | Reach (m,a1,a2,p)     -> append Bool [req_m m;req_a a1;req_a a2;req_p p]
    | ReachAt (m,a1,a2,l,p) -> append Bool [req_m m;req_a a1;req_a a2;req_i l;req_p p]
    | In (a,s)              -> append Bool [req_a a;req_s s]
    | SubsetEq (s1,s2)      -> append Bool [req_s s1;req_s s2]
    | InTh (t,s)            -> append Bool [req_t t;req_st s]
    | SubsetEqTh (s1,s2)    -> append Bool [req_st s1;req_st s2]
    | InInt (i,s)           -> append Bool [req_i i;req_si s]
    | SubsetEqInt (s1,s2)   -> append Bool [req_si s1;req_si s2]
    | Less (i1,i2)          -> append Bool [req_i i1;req_i i2]
    | Greater (i1,i2)       -> append Bool [req_i i1;req_i i2]
    | LessEq (i1,i2)        -> append Bool [req_i i1;req_i i2]
    | GreaterEq (i1,i2)     -> append Bool [req_i i1;req_i i2]
    | LessTid (t1,t2)       -> append Bool [req_t t1;req_t t2]
    | Eq (t1,t2)            -> union (req_term t1) (req_term t2)
    | InEq (t1,t2)          -> union (req_term t1) (req_term t2)
    | BoolVar _             -> single Bool
    | BoolArrayRd (a,t)     -> append Bool [req_arr a; req_t t]
    | _                     -> empty

  and req_m (m:mem) : SortSet.t =
    match m with
    | VarMem _         -> single Mem
    | Update (m,a,c)   -> append Mem [req_m m;req_a a;req_c c]
    | MemArrayRd (a,t) -> append Mem [req_arr a;req_t t]

  and req_p (p:path) : SortSet.t =
    match p with
    | VarPath _             -> single Path
    | Epsilon               -> single Path
    | SimplePath a          -> append Path [req_a a]
    | GetPath (m,a1,a2)     -> append Path [req_m m;req_a a1;req_a a2]
    | GetPathAt (m,a1,a2,l) -> append Path [req_m m;req_a a1;req_a a2;req_i l]
    | PathArrayRd (a,t)     -> append Path [req_arr a;req_t t]

  and req_si (s:setint) : SortSet.t =
    match s with
    | VarSetInt _         -> single SetInt
    | EmptySetInt         -> single SetInt
    | SinglInt i          -> append SetInt [req_i i]
    | UnionInt (s1,s2)    -> append SetInt [req_si s1;req_si s2]
    | IntrInt (s1,s2)     -> append SetInt [req_si s1;req_si s2]
    | SetdiffInt (s1,s2)  -> append SetInt [req_si s1;req_si s2]
    | SetIntArrayRd (a,t) -> append SetInt [req_arr a;req_t t]

  and req_se (s:setelem) : SortSet.t =
    match s with
    | VarSetElem _         -> single SetElem
    | EmptySetElem         -> single SetElem
    | SinglElem e          -> append SetElem [req_e e]
    | UnionElem (s1,s2)    -> append SetElem [req_se s1;req_se s2]
    | IntrElem (s1,s2)     -> append SetElem [req_se s1;req_se s2]
    | SetdiffElem (s1,s2)  -> append SetElem [req_se s1;req_se s2]
    | SetToElems (s,m)     -> append SetElem [req_s   s;req_m   m]
    | SetElemArrayRd (a,t) -> append SetElem [req_arr a;req_t   t]

  and req_st (s:setth) : SortSet.t =
    match s with
    | VarSetTh _         -> single SetTh
    | EmptySetTh         -> single SetTh
    | SinglTh t          -> append SetTh [req_t t]
    | UnionTh (s1,s2)    -> append SetTh [req_st s1;req_st s2]
    | IntrTh (s1,s2)     -> append SetTh [req_st s1;req_st s2]
    | SetdiffTh (s1,s2)  -> append SetTh [req_st s1;req_st s2]
    | SetThArrayRd (a,t) -> append SetTh [req_arr a;req_t t]

  and req_c (c:cell) : SortSet.t =
    match c with
    | VarCell _            -> single Cell
    | Error                -> single Cell
    | MkCell (e,a,t)       -> append Cell [req_e e;req_a a; req_t t]
    | MkSLKCell (e,aa,tt)  -> append Cell
                                ((List.map req_a aa) @
                                 (List.map req_t tt) @
                                 [req_e e])
    | MkSLCell (e,aa,ta,l) -> append Cell [req_e e;req_addrarr aa;
                                           req_tidarr ta;req_i l]
    | CellLock (c,t)       -> append Cell [req_c c;req_t t]
    | CellLockAt (c,l,t)   -> append Cell [req_c c;req_i l;req_t t]
    | CellUnlock c         -> append Cell [req_c c]
    | CellUnlockAt (c,l)   -> append Cell [req_c c;req_i l]
    | CellAt (m,a)         -> append Cell [req_m m;req_a a]
    | CellArrayRd (a,t)    -> append Cell [req_arr a;req_t t]
    | UpdCellAddr (c,i,a)  -> append Cell [req_c c; req_i i; req_a a]

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _             -> single Addr
    | Null                  -> single Addr
    | Next c                -> append Addr [req_c c]
    | NextAt (c,l)          -> append Addr [req_c c;req_i l]
    | ArrAt (c,l)           -> append Addr [req_c c;req_i l]
    | FirstLocked (m,p)     -> append Addr [req_m m;req_p p]
    | FirstLockedAt (m,p,l) -> append Addr [req_m m;req_p p;req_i l]
    | AddrArrayRd (a,t)     -> append Addr [req_arr a; req_t t]
    | AddrArrRd (a,i)       -> append Addr [req_addrarr a; req_i i]

  and req_e (e:elem) : SortSet.t =
    match e with
    | VarElem _         -> single Elem
    | CellData c        -> append Elem [req_c c]
    | ElemArrayRd (a,t) -> append Elem [req_arr a;req_t t]
    | HavocListElem     -> single Elem
    | HavocSkiplistElem -> single Elem
    | LowestElem        -> single Elem
    | HighestElem       -> single Elem

  and req_t (t:tid) : SortSet.t =
    match t with
    | VarTh _            -> single Tid
    | NoTid             -> single Tid
    | CellLockId c       -> append Tid [req_c c]
    | CellLockIdAt (c,l) -> append Tid [req_c c;req_i l]
    | TidArrayRd (a,t)  -> append Tid [req_arr a;req_t t]
    | TidArrRd (a,l)    -> append Tid [req_tidarr a;req_i l]

  and req_s (s:set) : SortSet.t =
    match s with
    | VarSet _            -> single Set
    | EmptySet            -> single Set
    | Singl a             -> append Set  [req_a a]
    | Union (s1,s2)       -> append Set [req_s s1;req_s s2]
    | Intr (s1,s2)        -> append Set [req_s s1;req_s s2]
    | Setdiff (s1,s2)     -> append Set [req_s s1;req_s s2]
    | PathToSet p         -> append Set [req_p p]
    | AddrToSet (m,a)     -> append Set [req_m m;req_a a]
    | AddrToSetAt (m,a,l) -> append Set [req_m m;req_a a;req_i l]
    | SetArrayRd (a,t)    -> append Set [req_arr a;req_t t]

  and req_i (i:integer) : SortSet.t =
    match i with
    | IntVal _         -> single Int
    | VarInt _         -> single Int
    | IntNeg i         -> append Int [req_i i]
    | IntAdd (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntSub (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntMul (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntDiv (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntArrayRd (a,t) -> append Int [req_arr a;req_t t]
    | IntSetMin s      -> append Int [req_si s]
    | IntSetMax s      -> append Int [req_si s]
    | CellMax c        -> append Int [req_c c]
    | HavocLevel       -> single Int

  and req_arr (a:arrays) : SortSet.t =
    match a with
    | VarArray _      -> single Array
    | ArrayUp (a,t,e) -> append Array [req_arr a;req_t t;req_expr e]

  and req_addrarr (a:addrarr) : SortSet.t =
    match a with
    | VarAddrArray _        -> single AddrArray
    | AddrArrayUp (arr,i,a) -> append AddrArray [req_addrarr arr;
                                                 req_i i;req_a a]
    | CellArr c             -> append AddrArray [req_c c]

  and req_tidarr (a:tidarr) : SortSet.t =
    match a with
    | VarTidArray _        -> single TidArray
    | TidArrayUp (arr,i,t) -> append TidArray [req_tidarr arr;
                                               req_i i;req_t t]
    | CellTids c             -> append TidArray [req_c c]

  and req_term (t:term) : SortSet.t =
    match t with
    | VarT v             -> single (V.sort v)
    | SetT s             -> req_s s
    | ElemT e            -> req_e e
    | TidT t             -> req_t t
    | AddrT a            -> req_a a
    | CellT c            -> req_c c
    | SetThT s           -> req_st s
    | SetIntT s          -> req_si s
    | SetElemT s         -> req_se s
    | PathT p            -> req_p p
    | MemT m             -> req_m m
    | IntT i             -> req_i i
    | ArrayT a           -> req_arr a
    | AddrArrayT a       -> req_addrarr a
    | TidArrayT a        -> req_tidarr a

  and req_expr (e:expr_t) : SortSet.t =
    match e with
    | Term t    -> req_term t
    | Formula f -> req_f f

  in
    SortSet.elements (req_f phi)


let gen_focus_list (max_pos:pc_t)
                   (focus_xs:pc_t list)
                   (ignore_xs:pc_t list) : (bool * pc_t list) =
  let full_xs = LeapLib.rangeList 0 max_pos in
  let base_pos_list = if focus_xs = [] then full_xs else focus_xs in
  let base_pos_set = List.fold_left (fun s p ->
    PosSet.add p s
  ) PosSet.empty base_pos_list in
  let focus_set = List.fold_left (fun s p ->
    PosSet.remove p s) base_pos_set ignore_xs in
  let consider_theta = PosSet.mem 0 focus_set in
  let focus_set_without_zero = PosSet.remove 0 focus_set in
  (consider_theta, (PosSet.elements focus_set_without_zero))


let formula_to_human_str (phi:formula) : string =
  let primed_varset = List.map V.prime (primed_vars phi) in
  let loc_vars_subs = V.new_subst () in
  List.iter (fun v ->
    let new_v = V.to_simple_str v in
    V.add_subst loc_vars_subs v (build_global_var new_v (V.sort v))
  ) (all_local_vars phi @ primed_varset);
  let f_without_locals = subst_vars loc_vars_subs phi in

  let vars_str = String.concat "\n"
                  (List.map (fun v ->
                     (sort_to_str (V.sort v)) ^ " " ^
                     (V.to_str v)
                   ) ((all_vars f_without_locals) @
                      (primed_vars f_without_locals))) in
  let f_str = match f_without_locals with
              | F.Implies (ante, conse) -> sprintf ("\n//antecedent:\n%s\n -> \n//consequent:\n%s") (formula_to_str ante) (formula_to_str conse)
              | _ -> formula_to_str f_without_locals in
  let full_str = "\nvars:\n\n" ^ vars_str ^ "\nformula:\n\n" ^ f_str in
  full_str





(* CONVERSION TO FOL FORMULA *)
(* Converts var'(k) into var_prime_k and PC into integer variables *)
(* Notice you are loosing preservation of others PC as they are not any longer arrays *)

let rec to_plain_var (v:V.t) : V.t =
  let plain_th = to_plain_shared_or_local
                    {fol_pc=true; fol_var=to_plain_var;} (V.parameter v) in
  let new_id = V.to_simple_str (V.set_param v plain_th) in
  build_var new_id (V.sort v) (V.is_primed v) V.Shared V.GlobalScope
(*
  build_var id s false V.Shared V.GlobalScope


  let new_v = build_global_var new_id (V.sort v) in
  if V.is_primed v then
    V.prime new_v
  else
    new_v
*)


and to_plain_shared_or_local (ops:fol_ops_t) (th:V.shared_or_local) : V.shared_or_local =
  match th with
  | V.Shared  -> V.Shared
  | V.Local t -> V.Local (ops.fol_var t)


and build_pc_var (pr:bool) (th:V.shared_or_local) : V.t =
  let pr_str = if pr then "_prime" else "" in
  let th_str = match th with
               | V.Shared-> ""
               | V.Local t -> "_" ^ (V.to_simple_str t)
  in
    build_global_var ("pc" ^ pr_str ^ th_str) Int


and to_plain_term (ops:fol_ops_t) (expr:term) : term =
  match expr with
    VarT(v)           -> VarT       (ops.fol_var v)
  | SetT(set)         -> SetT       (to_plain_set ops set)
  | AddrT(addr)       -> AddrT      (to_plain_addr ops addr)
  | ElemT(elem)       -> ElemT      (to_plain_elem ops elem)
  | TidT(th)         -> TidT      (to_plain_tid ops th)
  | CellT(cell)       -> CellT      (to_plain_cell ops cell)
  | SetThT(setth)     -> SetThT     (to_plain_setth ops setth)
  | SetIntT(setint)   -> SetIntT    (to_plain_setint ops setint)
  | SetElemT(setelem) -> SetElemT   (to_plain_setelem ops setelem)
  | PathT(path)       -> PathT      (to_plain_path ops path)
  | MemT(mem)         -> MemT       (to_plain_mem ops mem)
  | IntT(i)           -> IntT       (to_plain_int ops i)
  | ArrayT(arr)       -> ArrayT     (to_plain_arrays ops arr)
  | AddrArrayT(arr)   -> AddrArrayT (to_plain_addrarr ops arr)
  | TidArrayT(arr)    -> TidArrayT  (to_plain_tidarr ops arr)


and to_plain_expr(ops:fol_ops_t) (expr:expr_t): expr_t =
  match expr with
    Term t    -> Term (to_plain_term ops t)
  | Formula b -> Formula (to_plain_formula_aux ops b)


and to_plain_arrays (ops:fol_ops_t) (arr:arrays) : arrays =
  match arr with
    VarArray v      -> VarArray (ops.fol_var v)
      (*TODO: Fix open array case for array variables *)
      (* ALE: Translating ArrayUp to single variable update.
              That is, v' = v{t <- a} is translated into v_prime = a.
              This translation is done at literal level, hence this case
              should not appear at that is why I am asserting false. *)
  | ArrayUp(aa,t,e) -> (print_endline (arrays_to_str arr); assert false)
(*
                        ArrayUp(to_plain_arrays ops aa,
                                to_plain_tid ops t,
                                to_plain_expr ops e)
*)


and to_plain_addrarr (ops:fol_ops_t) (arr:addrarr) : addrarr =
  match arr with
    VarAddrArray v       -> VarAddrArray (ops.fol_var v)
      (*TODO: Fix open array case for array variables *)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(to_plain_addrarr ops arr,
                                        to_plain_int ops i,
                                        to_plain_addr ops a)
  | CellArr c            -> CellArr (to_plain_cell ops c)


and to_plain_tidarr (ops:fol_ops_t) (arr:tidarr) : tidarr =
  match arr with
    VarTidArray v       -> VarTidArray (ops.fol_var v)
      (*TODO: Fix open array case for array variables *)
  | TidArrayUp(arr,i,t) -> TidArrayUp(to_plain_tidarr ops arr,
                                      to_plain_int ops i,
                                      to_plain_tid ops t)
  | CellTids c            -> CellTids (to_plain_cell ops c)


and to_plain_set (ops:fol_ops_t) (e:set) : set =
  match e with
    VarSet v             -> VarSet (ops.fol_var v)
  | EmptySet             -> EmptySet
  | Singl(addr)          -> Singl(to_plain_addr ops addr)
  | Union(s1,s2)         -> Union(to_plain_set ops s1,
                                  to_plain_set ops s2)
  | Intr(s1,s2)          -> Intr(to_plain_set ops s1,
                                 to_plain_set ops s2)
  | Setdiff(s1,s2)       -> Setdiff(to_plain_set ops s1,
                                    to_plain_set ops s2)
  | PathToSet(path)      -> PathToSet(to_plain_path ops path)
  | AddrToSet(mem,addr)  -> AddrToSet(to_plain_mem ops mem,
                                      to_plain_addr ops addr)
  | AddrToSetAt(mem,a,l) -> AddrToSetAt(to_plain_mem ops mem,
                                        to_plain_addr ops a,
                                        to_plain_int ops l)
  | SetArrayRd(arr,t)    -> SetArrayRd(to_plain_arrays ops arr,
                                       to_plain_tid ops t)


and to_plain_addr (ops:fol_ops_t) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr (ops.fol_var v)
  | Null                      -> Null
  | Next(cell)                -> Next(to_plain_cell ops cell)
  | NextAt(cell,l)            -> NextAt(to_plain_cell ops cell,
                                        to_plain_int ops l)
  | ArrAt(cell,l)             -> ArrAt(to_plain_cell ops cell,
                                       to_plain_int ops l)
  | FirstLocked(mem,path)     -> FirstLocked(to_plain_mem ops mem,
                                             to_plain_path ops path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(to_plain_mem ops mem,
                                               to_plain_path ops path,
                                               to_plain_int ops l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(to_plain_arrays ops arr,
                                             to_plain_tid ops t)
  | AddrArrRd(arr,l)          -> AddrArrRd(to_plain_addrarr ops arr,
                                           to_plain_int ops l)


and to_plain_elem (ops:fol_ops_t) (e:elem) : elem =
  match e with
    VarElem v            -> VarElem (ops.fol_var v)
  | CellData(cell)       -> CellData(to_plain_cell ops cell)
  | ElemArrayRd(arr,t)   -> ElemArrayRd(to_plain_arrays ops arr,
                                        to_plain_tid ops t)
  | HavocListElem        -> HavocListElem
  | HavocSkiplistElem    -> HavocSkiplistElem
  | LowestElem           -> LowestElem
  | HighestElem          -> HighestElem


and to_plain_tid (ops:fol_ops_t) (th:tid) : tid =
  match th with
    VarTh v              -> VarTh (ops.fol_var v)
  | NoTid                -> NoTid
  | CellLockId(cell)     -> CellLockId(to_plain_cell ops cell)
  | CellLockIdAt(cell,l) -> CellLockIdAt(to_plain_cell ops cell,
                                         to_plain_int ops l)
  | TidArrayRd(arr,t)   -> TidArrayRd(to_plain_arrays ops arr,
                                        to_plain_tid ops t)
  | TidArrRd(arr,l)     -> TidArrRd(to_plain_tidarr ops arr,
                                      to_plain_int ops l)


and to_plain_cell (ops:fol_ops_t) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (ops.fol_var v)
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(to_plain_elem ops data,
                                   to_plain_addr ops addr,
                                   to_plain_tid ops th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(to_plain_elem ops data,
                                        List.map (to_plain_addr ops) aa,
                                        List.map (to_plain_tid ops) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(to_plain_elem ops data,
                                       to_plain_addrarr ops aa,
                                       to_plain_tidarr ops ta,
                                       to_plain_int ops l)
  | CellLock(cell,t)       -> CellLock(to_plain_cell ops cell,
                                       to_plain_tid ops t)
  | CellLockAt(cell,l, t)  -> CellLockAt(to_plain_cell ops cell,
                                         to_plain_int ops l,
                                         to_plain_tid ops t)
  | CellUnlock(cell)       -> CellUnlock(to_plain_cell ops cell)
  | CellUnlockAt(cell,l)   -> CellUnlockAt(to_plain_cell ops cell,
                                           to_plain_int ops l)
  | CellAt(mem,addr)       -> CellAt(to_plain_mem ops mem,
                                     to_plain_addr ops addr)
  | CellArrayRd(arr,t)     -> CellArrayRd(to_plain_arrays ops arr,
                                          to_plain_tid ops t)
  | UpdCellAddr(c,i,a)     -> UpdCellAddr(to_plain_cell ops c,
                                          to_plain_int ops i,
                                          to_plain_addr ops a)


and to_plain_setth (ops:fol_ops_t) (s:setth) : setth =
  match s with
    VarSetTh v            -> VarSetTh (ops.fol_var v)
  | EmptySetTh            -> EmptySetTh
  | SinglTh(th)           -> SinglTh(to_plain_tid ops th)
  | UnionTh(s1,s2)        -> UnionTh(to_plain_setth ops s1,
                                     to_plain_setth ops s2)
  | IntrTh(s1,s2)         -> IntrTh(to_plain_setth ops s1,
                                    to_plain_setth ops s2)
  | SetdiffTh(s1,s2)      -> SetdiffTh(to_plain_setth ops s1,
                                       to_plain_setth ops s2)
  | SetThArrayRd(arr,t)   -> SetThArrayRd(to_plain_arrays ops arr,
                                          to_plain_tid ops t)


and to_plain_setint (ops:fol_ops_t) (s:setint) : setint =
  match s with
    VarSetInt v            -> VarSetInt (ops.fol_var v)
  | EmptySetInt            -> EmptySetInt
  | SinglInt(i)            -> SinglInt(to_plain_int ops i)
  | UnionInt(s1,s2)        -> UnionInt(to_plain_setint ops s1,
                                       to_plain_setint ops s2)
  | IntrInt(s1,s2)         -> IntrInt(to_plain_setint ops s1,
                                    to_plain_setint ops s2)
  | SetdiffInt(s1,s2)      -> SetdiffInt(to_plain_setint ops s1,
                                       to_plain_setint ops s2)
  | SetIntArrayRd(arr,t)   -> SetIntArrayRd(to_plain_arrays ops arr,
                                            to_plain_tid ops t)


and to_plain_setelem (ops:fol_ops_t) (s:setelem) : setelem =
  match s with
    VarSetElem v            -> VarSetElem (ops.fol_var v)
  | EmptySetElem            -> EmptySetElem
  | SinglElem(e)            -> SinglElem(to_plain_elem ops e)
  | UnionElem(s1,s2)        -> UnionElem(to_plain_setelem ops s1,
                                         to_plain_setelem ops s2)
  | IntrElem(s1,s2)         -> IntrElem(to_plain_setelem ops s1,
                                        to_plain_setelem ops s2)
  | SetdiffElem(s1,s2)      -> SetdiffElem(to_plain_setelem ops s1,
                                           to_plain_setelem ops s2)
  | SetToElems(s,m)         -> SetToElems(to_plain_set ops s, to_plain_mem ops m)
  | SetElemArrayRd(arr,t)   -> SetElemArrayRd(to_plain_arrays ops arr,
                                              to_plain_tid ops t)


and to_plain_path (ops:fol_ops_t) (path:path) : path =
  match path with
    VarPath v                        -> VarPath (ops.fol_var v)
  | Epsilon                          -> Epsilon
  | SimplePath(addr)                 -> SimplePath(to_plain_addr ops addr)
  | GetPath(mem,add_from,add_to)     -> GetPath(to_plain_mem ops mem,
                                                to_plain_addr ops add_from,
                                                to_plain_addr ops add_to)
  | GetPathAt(mem,add_from,add_to,l) -> GetPathAt(to_plain_mem ops mem,
                                                  to_plain_addr ops add_from,
                                                  to_plain_addr ops add_to,
                                                  to_plain_int ops l)
  | PathArrayRd(arr,t)           -> PathArrayRd(to_plain_arrays ops arr,
                                                to_plain_tid ops t)


and to_plain_mem (ops:fol_ops_t) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem (ops.fol_var v)
  | Update(mem,add,cell) -> Update(to_plain_mem ops mem,
                                   to_plain_addr ops add,
                                   to_plain_cell ops cell)
  | MemArrayRd(arr,t)    -> MemArrayRd(to_plain_arrays ops arr,
                                       to_plain_tid ops t)


and to_plain_int (ops:fol_ops_t) (i:integer) : integer =
  match i with
    IntVal(i)           -> IntVal(i)
  | VarInt v            -> VarInt (ops.fol_var v)
  | IntNeg(i)           -> IntNeg(to_plain_int ops i)
  | IntAdd(i1,i2)       -> IntAdd(to_plain_int ops i1,
                                  to_plain_int ops i2)
  | IntSub(i1,i2)       -> IntSub(to_plain_int ops i1,
                                  to_plain_int ops i2)
  | IntMul(i1,i2)       -> IntMul(to_plain_int ops i1,
                                  to_plain_int ops i2)
  | IntDiv(i1,i2)       -> IntDiv(to_plain_int ops i1,
                                  to_plain_int ops i2)
  | IntArrayRd(arr,t)   -> IntArrayRd(to_plain_arrays ops arr,
                                      to_plain_tid ops t)
  | IntSetMin(s)        -> IntSetMin(to_plain_setint ops s)
  | IntSetMax(s)        -> IntSetMax(to_plain_setint ops s)
  | CellMax(c)          -> CellMax(to_plain_cell ops c)
  | HavocLevel          -> HavocLevel


and to_plain_atom (ops:fol_ops_t) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                 -> Append(to_plain_path ops p1,
                                                 to_plain_path ops p2,
                                                 to_plain_path ops pres)
  | Reach(h,add_from,add_to,p)         -> Reach(to_plain_mem ops h,
                                                to_plain_addr ops add_from,
                                                to_plain_addr ops add_to,
                                                to_plain_path ops p)
  | ReachAt(h,a_from,a_to,l,p)         -> ReachAt(to_plain_mem ops h,
                                                  to_plain_addr ops a_from,
                                                  to_plain_addr ops a_to,
                                                  to_plain_int ops l,
                                                  to_plain_path ops p)
  | OrderList(h,a_from,a_to)           -> OrderList(to_plain_mem ops h,
                                                    to_plain_addr ops a_from,
                                                    to_plain_addr ops a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Skiplist(to_plain_mem ops h,
                                                   to_plain_set ops s,
                                                   to_plain_int ops l,
                                                   to_plain_addr ops a_from,
                                                   to_plain_addr ops a_to,
                                                   to_plain_setelem ops elems)
  | In(a,s)                            -> In(to_plain_addr ops a,
                                             to_plain_set ops s)
  | SubsetEq(s_in,s_out)               -> SubsetEq(to_plain_set ops s_in,
                                                   to_plain_set ops s_out)
  | InTh(th,s)                         -> InTh(to_plain_tid ops th,
                                               to_plain_setth ops s)
  | SubsetEqTh(s_in,s_out)             -> SubsetEqTh(to_plain_setth ops s_in,
                                                     to_plain_setth ops s_out)
  | InInt(i,s)                         -> InInt(to_plain_int ops i,
                                                to_plain_setint ops s)
  | SubsetEqInt(s_in,s_out)            -> SubsetEqInt(to_plain_setint ops s_in,
                                                      to_plain_setint ops s_out)
  | InElem(e,s)                        -> InElem(to_plain_elem ops e,
                                                 to_plain_setelem ops s)
  | SubsetEqElem(s_in,s_out)           -> SubsetEqElem(to_plain_setelem ops s_in,
                                                       to_plain_setelem ops s_out)
  | Less(i1,i2)                        -> Less(to_plain_int ops i1,
                                               to_plain_int ops i2)
  | Greater(i1,i2)                     -> Greater(to_plain_int ops i1,
                                                  to_plain_int ops i2)
  | LessEq(i1,i2)                      -> LessEq(to_plain_int ops i1,
                                                 to_plain_int ops i2)
  | GreaterEq(i1,i2)                   -> GreaterEq(to_plain_int ops i1,
                                                    to_plain_int ops i2)
  | LessTid(t1,t2)                     -> LessTid(to_plain_tid ops t1,
                                                  to_plain_tid ops t2)
  | LessElem(e1,e2)                    -> LessElem(to_plain_elem ops e1,
                                                   to_plain_elem ops e2)
  | GreaterElem(e1,e2)                 -> GreaterElem(to_plain_elem ops e1,
                                                      to_plain_elem ops e2)
  | Eq(exp)                            -> Eq(to_plain_eq ops exp)
  | InEq(exp)                          -> InEq(to_plain_ineq ops exp)
  | BoolVar v                          -> BoolVar (ops.fol_var v)
  | BoolArrayRd(arr,t)                 -> BoolArrayRd(to_plain_arrays ops arr,
                                                      to_plain_tid ops t)
  | PC (pc,th,p)                       -> if ops.fol_pc then
                                            let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                                              Eq(IntT(VarInt pc_var),IntT(IntVal pc))
                                          else
                                            PC (pc,to_plain_shared_or_local ops th,p)
  | PCUpdate (pc,t)                    -> if ops.fol_pc then
                                            let pc_prime_var = build_pc_var true (V.Local (voc_to_var (to_plain_tid ops t))) in
                                              Eq (IntT (VarInt pc_prime_var), IntT (IntVal pc))
                                          else
                                            PCUpdate (pc, to_plain_tid ops t)
  | PCRange (pc1,pc2,th,p)             -> if ops.fol_pc then
                                            (assert false)
                                          else
                                            PCRange (pc1,pc2,to_plain_shared_or_local ops th,p)


and to_plain_literal (ops:fol_ops_t) (l:literal) : literal =
  match l with
  | F.Atom a    -> F.Atom    (to_plain_atom ops a)
  | F.NegAtom a -> F.NegAtom (to_plain_atom ops a)


and to_plain_eq (ops:fol_ops_t) ((t1,t2):eq) : eq =
  (to_plain_term ops t1, to_plain_term ops t2)


and to_plain_ineq (ops:fol_ops_t) ((t1,t2):diseq) : diseq =
  (to_plain_term ops t1, to_plain_term ops t2)

    
and to_plain_formula_aux (ops:fol_ops_t) (phi:formula) : formula =
  match phi with
  | F.True           -> F.True
  | F.False          -> F.False
  | F.And(f1,f2)     -> F.And(to_plain_formula_aux ops f1, to_plain_formula_aux ops f2)
  | F.Or(f1,f2)      -> F.Or(to_plain_formula_aux ops f1, to_plain_formula_aux ops f2)
  | F.Not(f)         -> F.Not(to_plain_formula_aux ops f)
  | F.Implies(f1,f2) -> F.Implies(to_plain_formula_aux ops f1, to_plain_formula_aux ops f2)
  | F.Iff (f1,f2)    -> F.Iff(to_plain_formula_aux ops f1, to_plain_formula_aux ops f2)
  | F.Literal l      -> begin
                        let conv_lit (lit:literal) : formula =
                          begin
                            match lit with
                              (* Update of a local variable of a parametrized system *)
                            | F.Atom(Eq(v',ArrayT(ArrayUp(arr,t,e))))
                            | F.Atom(Eq(ArrayT(ArrayUp(arr,t,e)),v'))
                            | F.NegAtom(InEq(v',ArrayT(ArrayUp(arr,t,e))))
                            | F.NegAtom(InEq(ArrayT(ArrayUp(arr,t,e)),v')) ->
                                let new_v' = V.prime (V.set_param (term_to_var v') (V.Local (voc_to_var t))) in
                                let as_var = to_plain_var (V.set_sort new_v' Bool) in
                                begin
                                  match to_plain_expr ops e with
                                  | Term ter -> let s = term_sort ter in
                                                let as_term = to_plain_term ops (var_to_term
                                                                (V.set_sort new_v' s)) in
                                                eq_term as_term ter
                                  | Formula F.True -> F.Literal (F.Atom (BoolVar as_var))
                                  | Formula F.False -> F.Literal (F.NegAtom (BoolVar as_var))
                                  | Formula phi -> F.Iff (F.Literal (F.Atom (BoolVar as_var )), phi)
                                end
                            | _ -> F.Literal(to_plain_literal ops lit)
                          end in
                        if ops.fol_pc then begin
                          match l with
                          | F.Atom(PCRange(pc1,pc2,th,p)) ->
                              let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                                F.And (lesseq_form (IntVal pc1) (VarInt pc_var),
                                       lesseq_form (VarInt pc_var) (IntVal pc2))
                          | F.NegAtom(PCRange(pc1,pc2,th,p)) ->
                              let pc_var = build_pc_var p (to_plain_shared_or_local ops th) in
                                F.Or (less_form (VarInt pc_var) (IntVal pc1),
                                      less_form (IntVal pc2) (VarInt pc_var))
                          | _ -> conv_lit l
                        end else
                          conv_lit l
                      end



and to_plain_formula (fol_mode:fol_mode_t) (phi:formula) : formula =
  match fol_mode with
  | PCOnly   -> to_plain_formula_aux {fol_pc=true;  fol_var=id;        } phi
  | VarsOnly -> to_plain_formula_aux {fol_pc=false; fol_var=to_plain_var;} phi
  | PCVars   -> to_plain_formula_aux {fol_pc=true;  fol_var=to_plain_var;} phi



let rec identical_formula  (phi1:formula) (phi2:formula) : bool =
  match (phi1,phi2) with
  | F.Literal l1, F.Literal l2 -> identical_literal l1 l2
  | F.True,  F.True -> true
  | F.False, F.False -> true
  | F.And(a1,a2),F.And(b1,b2) -> (identical_formula a1 b1 && identical_formula a2 b2) ||
                                 (identical_formula a1 b2 && identical_formula a2 b1)
  | F.Or(a1,a2),F.Or(b1,b2) -> (identical_formula a1 b1 && identical_formula a2 b2) ||
                               (identical_formula a1 b2 && identical_formula a2 b1)
  | F.Not(a), F.Not(b) -> identical_formula a b
  | F.Implies(a1,a2),F.Implies(b1,b2) -> (identical_formula a1 b1 && identical_formula a2 b2)
  | F.Iff(a1,a2), F.Implies(b1,b2) -> (identical_formula a1 b1 && identical_formula a2 b2) ||
                                    (identical_formula a1 b2 && identical_formula a2 b1)
  | _,_ -> false

and identical_sorts     (s1:sort) (s2:sort) : bool =
  s1 = s2
and identical_variable (v1:V.t) (v2:V.t): bool =
  v1 = v2
and identical_term   (t1:term) (t2:term) : bool =
  t1 = t2
and identical_eq  (e1: eq) (e2:eq) : bool =
  let (a1,b1)=e1 in
  let (a2,b2)=e2 in
    (identical_term a1 a2 && identical_term b1 b2 ) ||
    (identical_term a1 b2 && identical_term b1 a2 )
and identical_diseq (e1: diseq) (e2: diseq) : bool =
  let (a1,b1)=e1 in
  let (a2,b2)=e2 in
    (identical_term a1 a2 && identical_term b1 b2 ) ||
    (identical_term a1 b2 && identical_term b1 a2 )
and identical_arrays (a1:arrays) (a2:arrays) : bool =
  match (a1,a2) with
  | VarArray(v1), VarArray(v2) -> identical_variable v1 v2
  | ArrayUp(b1,t1,e1),ArrayUp(b2,t2,e2) -> 
    identical_arrays b1 b2 && identical_tid t1 t2 && identical_expr_t e2 e2
  | _,_ -> false
and identical_addrarr (a1:addrarr) (a2:addrarr) : bool =
  match (a1,a2) with
  | VarAddrArray(v1),VarAddrArray(v2) -> identical_variable v1 v2
  | AddrArrayUp(b1,i1,ad1),AddrArrayUp(b2,i2,ad2) ->
     identical_addrarr b1 b2 && identical_integer i1 i2 && identical_addr ad1 ad2
  | CellArr(c1),CellArr(c2) -> identical_cell c1 c2
  | _,_ -> false
and identical_tidarr (ta1:tidarr) (ta2:tidarr) : bool =
  match (ta1,ta2) with
  | VarTidArray(v1),VarTidArray(v2) -> identical_variable v1 v2
  | TidArrayUp(b1,i1,t1),TidArrayUp(b2,i2,t2) ->
     identical_tidarr b1 b2 && identical_integer i1 i2 && identical_tid t1 t2
  | CellTids(c1),CellTids(c2) -> identical_cell c1 c2
  | _,_ -> false
and identical_integer (i1:integer) (i2:integer) : bool =
  match (i1,i2) with
    IntVal(val1),IntVal(val2)  -> val1 = val2
  | VarInt(v1),VarInt(v2) -> identical_variable v1 v2
  | IntNeg(a), IntNeg(b)  -> identical_integer a b
  | IntAdd(a1,b1),IntAdd(a2,b2) -> 
    (identical_integer a1 a2 && identical_integer b1 b2) ||
    (identical_integer a1 b2 && identical_integer b1 a2)
  | IntSub(a1,b1),IntSub(a2,b2) ->
    (identical_integer a1 a2 && identical_integer b1 b2) 
  | IntMul(a1,b1),IntMul(a2,b2) ->
    (identical_integer a1 a2 && identical_integer b1 b2) ||
    (identical_integer a1 b2 && identical_integer b1 a2)
  | IntDiv(a1,b1),IntMul(a2,b2) ->
    (identical_integer a1 a2 && identical_integer b1 b2) 
  | IntArrayRd(arr1,t1),IntArrayRd(arr2,t2) ->
    (identical_arrays arr1 arr2 && identical_tid t1 t2) 
  | IntSetMin s1,IntSetMin s2 -> identical_setint s1 s2
  | IntSetMax s1,IntSetMax s2 -> identical_setint s1 s2
  | CellMax c1, CellMax c2    -> identical_cell   c1 c2
  | HavocLevel,HavocLevel     -> true
  | _,_ -> false
and identical_set (s1:set) (s2:set) : bool =
  match (s1,s2) with
    VarSet(v1),VarSet(v2)   -> identical_variable v1 v2
  | EmptySet,EmptySet       -> true                    
  | Singl(add1),Singl(add2) -> identical_addr add1 add2
  | Union(sa1,sb1),Union(sa2,sb2) -> 
    (identical_set sa1 sa2 && identical_set sb1 sb2) ||
    (identical_set sa1 sb2 && identical_set sb1 sa2)
  | Intr (sa1,sb1),Intr (sa2,sb2) ->
    (identical_set sa1 sa2 && identical_set sb1 sb2) ||
    (identical_set sa1 sb2 && identical_set sb1 sa2)
  | Setdiff(sa1,sb1),Setdiff(sa2,sb2) -> (identical_set sa1 sa2 && identical_set sb1 sb2)
  | PathToSet(p1),PathToSet(p2) -> identical_path p1 p2
  | AddrToSet(m1,add1),AddrToSet(m2,add2) -> identical_mem m1 m2 && identical_addr add1 add2 
  | AddrToSetAt(m1,add1,i1),AddrToSetAt(m2,add2,i2) ->
    identical_mem m1 m2 && identical_addr add1 add2 && identical_integer i1 i2
  | SetArrayRd(arr1,t1) ,SetArrayRd(arr2,t2) ->
    identical_arrays arr1 arr2 && identical_tid t1 t2
  | _,_ -> false      

and identical_tid (t1:tid) (t2:tid) : bool =
  match t1,t2 with
    VarTh(v1),VarTh(v2) -> identical_variable v1 v2
  | NoTid,NoTid -> true
  | CellLockId(c1),CellLockId(c2)    -> identical_cell c1 c2
  | CellLockIdAt(c1,i1),CellLockIdAt(c2,i2) -> 
    ( identical_cell c1 c2 && identical_integer i1 i2)
  | TidArrayRd(arr1,t1),TidArrayRd(arr2,t2) ->
    identical_arrays arr1 arr2 && identical_tid t1 t2
  | TidArrRd(ta1,i1),TidArrRd(ta2,i2)  ->
    identical_tidarr ta1 ta2 && identical_integer i1 i2
  | _,_ -> false
and identical_elem (e1:elem) (e2: elem)  : bool =
  match e1,e2 with
    VarElem(v1),VarElem(v2) -> identical_variable v1 v2
  | CellData(c1),CellData(c2) ->  identical_cell c1 c2
  | ElemArrayRd(arr1,t1),ElemArrayRd(arr2,t2) -> 
    identical_arrays arr1 arr2 && identical_tid t1 t2
  | HavocListElem, HavocListElem -> true
  | HavocSkiplistElem, HavocSkiplistElem -> true
  | LowestElem,LowestElem -> true
  | HighestElem,HighestElem -> true
  | _,_ -> false
and identical_addr (ad1:addr) (ad2:addr) : bool =
  match ad1,ad2 with
    VarAddr(v1), VarAddr(v2) -> identical_variable v1 v2
  | Null, Null -> true
  | Next(c1),Next(c2) -> identical_cell c1 c2
  | ArrAt(c1,i1),ArrAt(c2,i2) -> identical_cell c1 c2 && identical_integer i1 i2
  | FirstLocked(m1,p1),FirstLocked(m2,p2) -> 
    identical_mem m1 m2 && identical_path p1 p2
  | FirstLockedAt(m1,p1,i1),FirstLockedAt(m2,p2,i2) ->
    identical_mem m1 m2 && identical_path p1 p2 && identical_integer i1 i2 
  | AddrArrayRd(a1,t1) ,AddrArrayRd(a2,t2)  ->
    identical_arrays a1 a2 && identical_tid t1 t2
  | AddrArrRd(aa1,i1), AddrArrRd(aa2,i2)  ->
    identical_addrarr aa1 aa2 && identical_integer i1 i2
  | _,_ -> false
and identical_cell (c1:cell)  (c2:cell)  : bool =
  match c1, c2 with
    VarCell(v1),VarCell(v2) -> identical_variable v1 v2
  | Error,Error -> true
  | MkCell(e1,a1,t1),MkCell(e2,a2,t2) -> 
    identical_elem e1 e2 && identical_addr a1 a2 && identical_tid t1 t2
  | MkSLKCell(e1,al1,tl1),MkSLKCell(e2,al2,tl2) ->
    let identical_addr_list l1 l2 = 
      List.fold_left2 (fun res a1 a2 -> if (not res) then false else identical_addr a1 a2) true l1 l2 in
    let identical_tid_list l1 l2 =
      List.fold_left2 (fun res t1 t2 -> if (not res) then false else identical_tid t1 t2) true l1 l2 in
    identical_elem e1 e2 && identical_addr_list al1 al2 && identical_tid_list tl1 tl2
  | MkSLCell(e1,ad1,ta1,i1),MkSLCell(e2,ad2,ta2,i2) ->
    identical_elem e1 e2 && identical_addrarr ad1 ad2 && identical_tidarr ta1 ta2 && identical_integer i1 i2
  | CellLock(c1,t1),CellLock(c2,t2) ->
      identical_cell c1 c2 && identical_tid t1 t2
  | CellLockAt(c1,i1,t1),CellLockAt(c2,i2,t2) ->
      identical_cell c1 c2 && identical_integer i1 i2 && identical_tid t1 t2
  | CellUnlock(c1), CellUnlock(c2) -> identical_cell c1 c2
  | CellUnlockAt(c1,i1),CellUnlockAt(c2,i2) ->
      identical_cell c1 c2 && identical_integer i1 i2
  | CellAt(m1,ad1),CellAt(m2,ad2) ->
      identical_mem m1 m2 && identical_addr ad1 ad2
  | CellArrayRd(ar1,t1),CellArrayRd(ar2,t2) ->
      identical_arrays ar1 ar2 && identical_tid t1 t2
  | _,_ -> false
and identical_setth (s1:setth) (s2: setth) : bool =
  match s1, s2 with
    VarSetTh(v1),VarSetTh(v2) -> identical_variable v1 v2
  | EmptySetTh,EmptySetTh -> true
  | SinglTh(t1),SinglTh(t2) -> identical_tid t1 t2
  | UnionTh(a1,b1),UnionTh(a2,b2)  -> 
    ( identical_setth a1 a2  && identical_setth b1 b2 ) ||
    ( identical_setth a1 b2  && identical_setth b1 a2 )
  | IntrTh(a1,b1),IntrTh(a2,b2)  ->
    ( identical_setth a1 a2  && identical_setth b1 b2 ) ||
    ( identical_setth a1 b2  && identical_setth b1 a2 )
  | SetdiffTh(a1,b1),SetdiffTh(a2,b2) ->
    ( identical_setth a1 a2  && identical_setth b1 b2 )
  | SetThArrayRd(ar1,t1),SetThArrayRd(ar2,t2) ->
    ( identical_arrays ar1 ar2  && identical_tid t1 t2 )
  | _,_ -> false

and identical_setint (s1:setint) (s2: setint) : bool =
  match s1, s2 with 
    VarSetInt(v1),VarSetInt(v2) -> identical_variable v1 v2
  | EmptySetInt,EmptySetInt -> true
  | SinglInt(i1),SinglInt(i2) -> identical_integer i1 i2
  | UnionInt(a1,b1),UnionInt(a2,b2) ->
    ( identical_setint a1 a2  && identical_setint b1 b2 ) ||
    ( identical_setint a1 b2  && identical_setint b1 a2 )
  | IntrInt(a1,b1),IntrInt(a2,b2) ->       
    ( identical_setint a1 a2  && identical_setint b1 b2 ) ||
    ( identical_setint a1 b2  && identical_setint b1 a2 )
  | SetdiffInt(a1,b1),SetdiffInt(a2,b2) ->
    ( identical_setint a1 a2  && identical_setint b1 b2 )
  | SetIntArrayRd(arr1,t1), SetIntArrayRd(arr2,t2) ->
    ( identical_arrays arr1 arr2  && identical_tid t1 t2 )
  | _,_ -> false
and identical_setelem (s1: setelem) (s2: setelem) : bool =
  match s1, s2 with
    VarSetElem(v1),VarSetElem(v2) -> identical_variable v1 v2
  | EmptySetElem,EmptySetElem -> true
  | SinglElem(e1),SinglElem(e2) -> identical_elem e1 e2
  | UnionElem(a1,b1),UnionElem(a2,b2) ->
    ( identical_setelem a1 a2  && identical_setelem b1 b2 ) ||
    ( identical_setelem a1 b2  && identical_setelem b1 a2 )
  | IntrElem(a1,b1),IntrElem(a2,b2) ->
    ( identical_setelem a1 a2  && identical_setelem b1 b2 ) ||
    ( identical_setelem a1 b2  && identical_setelem b1 a2 )
  | SetdiffElem(a1,b1),SetdiffElem(a2,b2) ->
    ( identical_setelem a1 a2  && identical_setelem b1 b2 )
  | SetToElems(s1,m1),SetToElems(s2,m2) ->
    identical_set s1 s2 && identical_mem m1 m2
  | SetElemArrayRd(arr1,t1),SetElemArrayRd(arr2,t2) ->
    identical_arrays arr1 arr2 && identical_tid t1 t2
  | _,_ -> false

and identical_path  (p1:path) (p2: path) : bool =
  match p1, p2 with
    VarPath(v1),VarPath(v2) -> identical_variable v1 v2
  | Epsilon,Epsilon -> true
  | SimplePath(ad1),SimplePath(ad2) -> identical_addr ad1 ad2
  | GetPath(m1,a1,b1),GetPath(m2,a2,b2) ->
    identical_mem m1 m2 && identical_addr a1 a2 && identical_addr b1 b2
  | GetPathAt(m1,a1,b1,i1),GetPathAt(m2,a2,b2,i2) ->
    identical_mem m1 m2 && identical_addr a1 a2 && identical_addr b1 b2 &&
      identical_integer i1 i2
  | PathArrayRd(ar1,t1),PathArrayRd(ar2,t2)->
    identical_arrays ar1 ar2 && identical_tid t1 t2
  | _,_ -> false
and identical_mem  (m1:mem) (m2: mem) : bool =
  match m1 ,m2 with
    VarMem(v1),VarMem(v2) -> identical_variable v1 v2
  | Update(m1,a1,c1),Update(m2,a2,c2) ->
    identical_mem m1 m2 && identical_addr a1 a2 && identical_cell c1 c2
  | MemArrayRd(ar1,t1),MemArrayRd(ar2,t2) ->
    identical_arrays ar1 ar2 && identical_tid t1 t2
  | _,_ -> false
and identical_atom (a1:atom) (a2: atom) : bool =
  match a1, a2 with
    Append(p1,q1,r1),Append(p2,q2,r2) ->
      identical_path p1 p2 && identical_path q1 q2 && identical_path r1 r2
  | Reach(m1,ad1,b1,p1),Reach(m2,ad2,b2,p2) ->
    identical_mem m1 m2 && identical_addr ad1 ad2 && identical_addr b1 b2 && identical_path p1 p2
  | ReachAt(m1,ad1,b1,i1,p1),ReachAt(m2,ad2,b2,i2,p2) ->
    identical_mem m1 m2 
    && identical_addr ad1 ad2 && identical_addr b1 b2 
    && identical_integer i1 i2 && identical_path p1 p2
  | OrderList(m1,ad1,b1),OrderList(m2,ad2,b2) ->
    identical_mem m1 m2 && identical_addr ad1 ad2 && identical_addr b1 b2
  | Skiplist(m1,s1,i1,ad1,b1,e1),Skiplist(m2,s2,i2,ad2,b2,e2) ->
    identical_mem m1 m2 && identical_set s1 s2 && identical_integer i1 i2
    && identical_addr ad1 ad2 && identical_addr b1 b2 && identical_setelem e1 e2
  | In(ad1,s1),In(ad2,s2) ->
    identical_addr ad1 ad2 && identical_set s1 s2
  | SubsetEq(s1,r1),SubsetEq(s2,r2) ->
    identical_set s1 s2 && identical_set r1 r2
  | InTh(t1,s1),InTh(t2,s2) ->
    identical_tid t1 t2 && identical_setth s1 s2
  | SubsetEqTh(s1,r1),SubsetEqTh(s2,r2) ->
    identical_setth s1 s2 && identical_setth r1 r2
  | InInt(i1,s1),InInt(i2,s2) ->
    identical_integer i1 i2 && identical_setint s1 s2
  | SubsetEqInt(s1,r1),SubsetEqInt(s2,r2) ->
    identical_setint s1 s2 &&    identical_setint r1 r2
  | InElem(e1,s1),InElem(e2,s2) ->
    identical_elem e1 e2 && identical_setelem s1 s2
  | SubsetEqElem(s1,r1),SubsetEqElem(s2,r2) ->
    identical_setelem s1 s2 && identical_setelem r1 r2
  | Less(n1,m1),Less(n2,m2) ->
    identical_integer n1 n2 && identical_integer m1 m2
  | Less(n1,m1),Greater(n2,m2) ->
    identical_integer n1 m2 && identical_integer m1 n2
  | Greater(n1,m1),Greater(n2,m2) ->
    identical_integer n1 n2 && identical_integer m1 m2
  | Greater(n1,m1),Less(n2,m2) ->
    identical_integer n1 m2 && identical_integer m1 n2
  | LessEq(n1,m1),LessEq(n2,m2) ->
    identical_integer n1 n2 && identical_integer m1 m2
  | LessEq(n1,m1),GreaterEq(n2,m2) ->
    identical_integer n1 m2 && identical_integer m1 n2
  | GreaterEq(n1,m1),GreaterEq(n2,m2) ->
    identical_integer n1 n2 && identical_integer m1 m2
  | GreaterEq(n1,m1),LessEq(n2,m2) ->
    identical_integer n1 m2 && identical_integer m1 n2
  | LessElem(n1,m1),LessElem(n2,m2) ->
    identical_elem n1 m1 && identical_elem n2 m2
  | LessElem(n1,m1),GreaterElem(n2,m2) ->
    identical_elem n1 m2 && identical_elem n2 m1
  | GreaterElem(n1,m1),GreaterElem(n2,m2) ->
    identical_elem n1 m1 && identical_elem n2 m2
  | GreaterElem(n1,m1),LessElem(n2,m2) ->
    identical_elem n1 m2 && identical_elem n2 m1
  | Eq(e1),Eq(e2) ->
    identical_eq e1 e2
  | InEq(e1),InEq(e2)->
    identical_diseq e1 e2
  | BoolVar(v1),BoolVar(v2) ->
    identical_variable v1 v2
  | BoolArrayRd(arr1,t1) ,BoolArrayRd(arr2,t2) ->
    identical_arrays arr1 arr2 && identical_tid t1 t2
  | PC(p1,V.Shared,b1),PC(p2,V.Shared,b2) ->
    identical_pc_t p1 p2 && b1=b2
  | PC(p1,V.Local t1,b1),PC(p2,V.Local t2,b2) ->
    identical_pc_t p1 p2 && b1=b2 && identical_variable t1 t2
  | PCUpdate(p1,t1),PCUpdate(p2,t2) ->
    identical_pc_t p1 p2 && identical_tid t1 t2
  | PCRange(p1,q1,V.Shared,b1),PCRange(p2,q2,V.Shared,b2) ->
    identical_pc_t p1 q1 && identical_pc_t p2 q2 && b1=b2
  | PCRange(p1,q1,V.Local t1,b1),PCRange(p2,q2,V.Local t2,b2) ->
    identical_pc_t p1 q1 && identical_pc_t p2 q2 && b1=b2 && identical_variable t1 t2
  | _,_ -> false
and opposite_literal (l1:literal) (l2:literal) : bool =
  match l1, l2 with
    F.Atom(a1), F.NegAtom(a2) -> identical_atom a1 a2
  | F.NegAtom(a1), F.Atom(a2) -> identical_atom a1 a2
  | _,_ -> false
and identical_literal (l1:literal) (l2: literal) : bool =
  match l1, l2 with
    F.Atom(a1),F.Atom (a2)      -> identical_atom a1 a2
  | F.NegAtom(a1),F.NegAtom(a2) -> identical_atom a1 a2
  | _,_ -> false
and identical_conjunctive_formula (f1:conjunctive_formula) (f2:conjunctive_formula) : bool =
  match f1,f2 with
    F.FalseConj,F.FalseConj -> true
  | F.TrueConj,F.TrueConj -> true
  | F.Conj l1, F.Conj l2 ->
    let some_is_identical c l = List.exists (fun d -> identical_literal c d) l in
       List.for_all (fun d -> some_is_identical d l2) l1 
    && List.for_all (fun d -> some_is_identical d l1) l2
  | _,_ -> false
and identical_expr_t  (e1:expr_t) (e2: expr_t)  : bool =
  match e1,e2 with
    Term(t1),Term(t2) -> identical_term t1 t2
  | Formula f1,Formula f2 -> identical_formula f1 f2
  | _,_ -> false
and identical_pc_t (p1:pc_t) (p2:pc_t) : bool =
  p1 = p2


let gen_fresh_var (gen:V.fresh_var_gen_t) (s:sort) : V.t =
  V.gen_fresh_var sort_to_str {nature = RealVar;} gen s

