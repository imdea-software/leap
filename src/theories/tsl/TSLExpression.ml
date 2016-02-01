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

type var_info_t =
  {
    treat_as_pc : bool;
  }

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = var_info_t
  end )


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
and literal = atom Formula.literal
and conjunctive_formula = atom Formula.conjunctive_formula
and disjunctive_formula = atom Formula.disjunctive_formula
and formula = atom Formula.formula

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
              ?(treat_as_pc=false)
              (id:V.id)
              (s:sort)
              (pr:bool)
              (th:V.shared_or_local)
              (p:V.procedure_name)
                 : V.t =
                   V.build id s pr th p {treat_as_pc = treat_as_pc;} ~fresh:fresh


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


(************************************************)
(*  Obtain the set of variables from a formula  *)
(************************************************)

let (@@) s1 s2 =
  V.VarSet.union s1 s2


let get_varset_from_param (v:V.t) : V.VarSet.t =
  match V.parameter v with
  | V.Local t -> V.VarSet.singleton t
  | V.Shared -> V.VarSet.empty


let rec get_varset_set (s:set) : V.VarSet.t =
  match s with
      VarSet v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySet         -> V.VarSet.empty
    | Singl(a)         -> get_varset_addr a
    | Union(s1,s2)     -> (get_varset_set s1) @@ (get_varset_set s2)
    | Intr(s1,s2)      -> (get_varset_set s1) @@ (get_varset_set s2)
    | Setdiff(s1,s2)   -> (get_varset_set s1) @@ (get_varset_set s2)
    | PathToSet(p)     -> get_varset_path p
    | AddrToSet(m,a,l) -> (get_varset_mem m)  @@
                          (get_varset_addr a) @@
                          (get_varset_integer l)

and get_varset_tid (th:tid) : V.VarSet.t=
  match th with
      VarTh v            -> V.VarSet.singleton v @@ get_varset_from_param v
    | NoTid              -> V.VarSet.empty
    | CellLockIdAt (c,l) -> (get_varset_cell c) @@ (get_varset_integer l)
    | TidArrRd (ta,i)    -> (get_varset_tidarr ta) @@ (get_varset_integer i)

and get_varset_elem (e:elem) : V.VarSet.t =
  match e with
      VarElem v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | CellData c        -> get_varset_cell c
    | HavocSkiplistElem -> V.VarSet.empty
    | LowestElem        -> V.VarSet.empty
    | HighestElem       -> V.VarSet.empty

and get_varset_addr (a:addr) : V.VarSet.t =
  match a with
      VarAddr v        -> V.VarSet.singleton v @@ get_varset_from_param v
    | Null             -> V.VarSet.empty
    | ArrAt (c,l)      -> (get_varset_cell c) @@ (get_varset_integer l)
    | AddrArrRd (aa,i) -> (get_varset_addrarr aa) @@ (get_varset_integer i)

and get_varset_cell (c:cell) : V.VarSet.t =
    match c with
      VarCell v           -> V.VarSet.singleton v @@ get_varset_from_param v
    | Error               -> V.VarSet.empty
    | MkCell(e,aa,tt,l)   -> (get_varset_elem e) @@ (get_varset_addrarr aa) @@
                             (get_varset_tidarr tt) @@ (get_varset_integer l)
    | CellLockAt (c,l,th) -> (get_varset_cell c) @@ (get_varset_integer l) @@
                             (get_varset_tid th)
    | CellUnlockAt (c,l)  -> (get_varset_cell c) @@ (get_varset_integer l)
    | CellAt(m,a)         -> (get_varset_mem  m) @@ (get_varset_addr a)

and get_varset_setth (sth:setth) : V.VarSet.t =
  match sth with
      VarSetTh v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySetTh         -> V.VarSet.empty
    | SinglTh(th)        -> (get_varset_tid th)
    | UnionTh(st1,st2)   -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | IntrTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | SetdiffTh(st1,st2) -> (get_varset_setth st1) @@ (get_varset_setth st2)

and get_varset_setelem (se:setelem) : V.VarSet.t =
  match se with
      VarSetElem v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySetElem         -> V.VarSet.empty
    | SinglElem(e)         -> (get_varset_elem e)
    | UnionElem(st1,st2)   -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | IntrElem(st1,st2)    -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | SetToElems(s,m)      -> (get_varset_set s) @@ (get_varset_mem m)
    | SetdiffElem(st1,st2) -> (get_varset_setelem st1) @@ (get_varset_setelem st2)

and get_varset_path (p:path) : V.VarSet.t =
  match p with
      VarPath v          -> V.VarSet.singleton v @@ get_varset_from_param v
    | Epsilon            -> V.VarSet.empty
    | SimplePath(a)      -> (get_varset_addr a)
    | GetPath(m,a1,a2,l) -> (get_varset_mem m)   @@
                            (get_varset_addr a1) @@
                            (get_varset_addr a2) @@
                            (get_varset_integer l)

and get_varset_mem (m:mem) : V.VarSet.t =
  match m with
      VarMem v           -> V.VarSet.singleton v @@ get_varset_from_param v
    | Update(m,a,c)      -> (get_varset_mem m) @@ (get_varset_addr a) @@ (get_varset_cell c)

and get_varset_integer (i:integer) : V.VarSet.t =
  match i with
      IntVal _     -> V.VarSet.empty
    | VarInt v     -> V.VarSet.singleton v
    | IntNeg i     -> (get_varset_integer i)
    | IntAdd (i,j) -> (get_varset_integer i) @@ (get_varset_integer j)
    | IntSub (i,j) -> (get_varset_integer i) @@ (get_varset_integer j)
    | IntMul (i,j) -> (get_varset_integer i) @@ (get_varset_integer j)
    | IntDiv (i,j) -> (get_varset_integer i) @@ (get_varset_integer j)
    | CellMax c    -> (get_varset_cell c)
    | HavocLevel   -> V.VarSet.empty

and get_varset_addrarr (arr:addrarr) : V.VarSet.t =
  match arr with
      VarAddrArray v       -> V.VarSet.singleton v
    | AddrArrayUp (aa,i,a) -> (get_varset_addrarr aa) @@
                              (get_varset_integer i)  @@
                              (get_varset_addr a)
    | CellArr c            -> (get_varset_cell c)


and get_varset_tidarr (arr:tidarr) : V.VarSet.t =
  match arr with
      VarTidArray v       -> V.VarSet.singleton v
    | TidArrayUp (aa,i,t) -> (get_varset_tidarr aa) @@
                             (get_varset_integer i) @@
                             (get_varset_tid t)
    | CellTids c          -> (get_varset_cell c)


and get_varset_atom (instances:bool) (a:atom) : V.VarSet.t =
  match a with
      Append(p1,p2,p3)         -> (get_varset_path p1) @@ (get_varset_path p2) @@
                                  (get_varset_path p3)
    | Reach(m,a1,a2,l,p)       -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                  (get_varset_addr a2) @@ (get_varset_integer l) @@
                                  (get_varset_path p)
    | OrderList(m,a1,a2)       -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                  (get_varset_addr a2)
    | Skiplist(m,s,l,a1,a2,es) -> (get_varset_mem m) @@
                                  (get_varset_set s) @@ (get_varset_integer l) @@
                                  (get_varset_addr a1) @@ (get_varset_addr a2) @@
                                  (get_varset_setelem es)
    | In(a,s)                  -> (get_varset_addr a) @@ (get_varset_set s)
    | SubsetEq(s1,s2)          -> (get_varset_set s1) @@ (get_varset_set s2)
    | InTh(th,st)              -> (get_varset_tid th) @@ (get_varset_setth st)
    | SubsetEqTh(st1,st2)      -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | InElem(e,se)             -> (get_varset_elem e) @@ (get_varset_setelem se)
    | SubsetEqElem(se1,se2)    -> (get_varset_setelem se1) @@
                                  (get_varset_setelem se2)
    | Less (i,j)               -> (get_varset_integer i) @@ (get_varset_integer j)
    | Greater (i,j)            -> (get_varset_integer i) @@ (get_varset_integer j)
    | LessEq (i,j)             -> (get_varset_integer i) @@ (get_varset_integer j)
    | GreaterEq (i,j)          -> (get_varset_integer i) @@ (get_varset_integer j)
    | LessElem(e1,e2)          -> (get_varset_elem e1) @@ (get_varset_elem e2)
    | GreaterElem(e1,e2)       -> (get_varset_elem e1) @@ (get_varset_elem e2)
    | Eq((x,y))                -> if instances then
                                    match (x,y) with
                                    | (VarUpdate _, _) -> get_varset_term instances x
                                    | (_, VarUpdate _) -> get_varset_term instances y
                                    | _ -> (get_varset_term instances x) @@
                                           (get_varset_term instances y)
                                  else
                                    (get_varset_term instances x) @@
                                    (get_varset_term instances y)
    | InEq((x,y))              -> (get_varset_term instances x) @@
                                  (get_varset_term instances y)
    | BoolVar v                -> (V.VarSet.singleton v)
    | PC(_,th,_)               -> (match th with
                                   | V.Shared -> V.VarSet.empty
                                   | V.Local t -> V.VarSet.singleton t)
    | PCUpdate (_,th)          -> (get_varset_tid th)
    | PCRange(_,_,th,_)        -> (match th with
                                   | V.Shared -> V.VarSet.empty
                                   | V.Local t -> V.VarSet.singleton t)

and get_varset_term (instances:bool) (t:term) : V.VarSet.t =
    match t with
      VarT   v            -> V.VarSet.singleton v @@ get_varset_from_param v
    | SetT   s            -> get_varset_set s
    | ElemT  e            -> get_varset_elem e
    | TidT  th            -> get_varset_tid th
    | AddrT  a            -> get_varset_addr a
    | CellT  c            -> get_varset_cell c
    | SetThT st           -> get_varset_setth st
    | SetElemT se         -> get_varset_setelem se
    | PathT  p            -> get_varset_path p
    | MemT   m            -> get_varset_mem m
    | IntT   i            -> get_varset_integer i
    | AddrArrayT aa       -> get_varset_addrarr aa
    | TidArrayT  tt       -> get_varset_tidarr tt
    | VarUpdate(v,_,t)    -> if instances then
                               get_varset_term instances t
                             else
                               (V.VarSet.singleton v) @@
                               (get_varset_term instances t) @@
                               (get_varset_from_param v)


let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun info a -> get_varset_atom info a)
                  (fun _ -> V.VarSet.empty)
                  (@@)


let get_varset_from_conj (instances:bool) (cf:conjunctive_formula) : V.VarSet.t =
  Formula.conjunctive_formula_fold varset_fs instances cf

let get_varset_from_formula (instances:bool) (phi:formula) : V.VarSet.t =
  Formula.formula_fold varset_fs instances phi


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


let get_termset_atom (a:atom) : TermSet.t =
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
  | PC(_,th,_)               -> (match th with
                                 | V.Shared  -> TermSet.empty
                                 | V.Local t -> add_list [TidT (VarTh t)])
  | PCUpdate (_,th)          -> add_list [TidT th]
  | PCRange(_,_,th,_)        -> (match th with
                                 | V.Shared  -> TermSet.empty
                                 | V.Local t -> add_list [TidT (VarTh t)])

let termset_fs = Formula.make_fold
                   Formula.GenericLiteralFold
                   (fun _ a -> get_termset_atom a)
                   (fun _ -> TermSet.empty)
                   (TermSet.union)

let get_termset_from_conjformula (cf:conjunctive_formula) : TermSet.t =
  Formula.conjunctive_formula_fold termset_fs () cf

let get_termset_from_formula (phi:formula) : TermSet.t =
  Formula.formula_fold termset_fs () phi


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
let is_var_path (p:path) : bool =
  match p with
  | VarPath(_) -> true
  | _          -> false
and is_var_addr (a:addr) : bool =
  match a with
  | VarAddr(_) -> true
  | _          -> false
and is_var_mem (m:mem) : bool =
  match m with
  | VarMem(_) -> true
  | _         -> false
and is_var_cell (c:cell) : bool =
  match c with
  | VarCell(_) -> true
  | _          -> false
and is_var_elem (e:elem) : bool =
  match e with
  | VarElem(_) -> true
  | _          -> false
and is_var_thid (t:tid) : bool =
  match t with
  | VarTh(_) -> true
  | _        -> false
and is_var_set (s:set) : bool =
  match s with
  | VarSet(_) -> true
  | _         -> false
and is_var_setth (s:setth) : bool =
  match s with
  | VarSetTh(_) -> true
  | _           -> false
and is_var_setelem (s:setelem) : bool =
  match s with
  | VarSetElem(_) -> true
  | _             -> false
and is_var_int (i:integer) : bool =
  match i with
  | VarInt(_) -> true
  | _         -> false
and is_var_addrarr (aa:addrarr) : bool =
  match aa with
  | VarAddrArray(_) -> true
  | _               -> false
and is_var_thidarr (tt:tidarr) : bool =
  match tt with
  | VarTidArray(_) -> true
  | _              -> false


let is_var_term (t:term) : bool =
  match t with
  | VarT(_)        -> true
  | SetT(s)        -> is_var_set s
  | ElemT(e)       -> is_var_elem e
  | TidT(t)        -> is_var_thid t
  | AddrT(a)       -> is_var_addr a
  | CellT(c)       -> is_var_cell c
  | SetThT(st)     -> is_var_setth st
  | SetElemT(st)   -> is_var_setelem st
  | PathT(p)       -> is_var_path p
  | MemT(m)        -> is_var_mem m
  | IntT(i)        -> is_var_int i
  | AddrArrayT(aa) -> is_var_addrarr aa
  | TidArrayT(tt)  -> is_var_thidarr tt
  | VarUpdate _    -> false



(* is_constant *)

let is_constant_set (s:set) : bool =
  match s with
  | EmptySet -> true
  | _        -> false
and is_constant_setth (s:setth) : bool =
  match s with
  | EmptySetTh -> true
  | _          -> false
and is_constant_setelem (s:setelem) : bool =
  match s with
  | EmptySetElem -> true
  | _            -> false
and is_constant_elem (e:elem) : bool =
  match e with
  | LowestElem  -> true
  | HighestElem -> true
  | _           -> false
and is_constant_thid (t:tid) : bool =
  match t with
  | NoTid -> true
  | _      -> false
and is_constant_addr (a:addr) : bool =
  match a with
  | Null -> true
  | _    -> false
and is_constant_cell (c:cell) : bool =
  match c with
  | Error -> true
  | _     -> false
and is_constant_path (p:path) : bool =
  match p with
  | Epsilon -> true
  | _       -> false
and is_constant_int (i:integer) : bool =
  match i with
  | IntVal _ -> true
  | _        -> false

let is_constant_term (t:term) : bool =
  match t with
  | VarT(_)        -> false
  | SetT(s)        -> is_constant_set s
  | ElemT(e)       -> is_constant_elem e
  | TidT(th)       -> is_constant_thid th
  | AddrT(a)       -> is_constant_addr a
  | CellT(c)       -> is_constant_cell c
  | SetThT(st)     -> is_constant_setth st
  | SetElemT(st)   -> is_constant_setelem st
  | PathT(p)       -> is_constant_path p
  | MemT _         -> false
  | IntT(i)        -> is_constant_int i
  | AddrArrayT _   -> false
  | TidArrayT _    -> false
  | VarUpdate _    -> false


let is_ineq_normalized a b =
  (is_var_term a || is_var_term b)

let is_eq_normalized a b =
  (is_var_term a || is_var_term b)


(* TODO: propagate equalities of vars x = y *)
let rec is_term_flat t =
  match t with
      VarT(_)        -> true
    | SetT s         -> is_set_flat s
    | ElemT e        -> is_elem_flat   e
    | TidT k         -> is_tid_flat k
    | AddrT a        -> is_addr_flat a
    | CellT c        -> is_cell_flat c
    | SetThT st      -> is_setth_flat st
    | SetElemT se    -> is_setelem_flat se
    | PathT p        -> is_path_flat p
    | MemT  m        -> is_mem_flat m
    | IntT  i        -> is_int_flat i
    | AddrArrayT aa  -> is_addrarr_flat aa
    | TidArrayT tt   -> is_tidarr_flat tt
    | VarUpdate _    -> false

and is_set_flat t =
  match t with
      VarSet _         -> true
    | EmptySet         -> true
    | Singl(a)         -> is_addr_flat  a
    | Union(s1,s2)     -> (is_set_flat s1) && (is_set_flat s2)
    | Intr(s1,s2)      -> (is_set_flat s1) && (is_set_flat s2)
    | Setdiff(s1,s2)   -> (is_set_flat s1) && (is_set_flat s2)
    | PathToSet(p)     -> (is_path_flat p)
    | AddrToSet(m,a,l) -> (is_mem_flat m) && (is_addr_flat a) && (is_int_flat l)
and is_tid_flat t =
  match t with
      VarTh _            -> true
    | NoTid              -> true
    | CellLockIdAt (c,l) -> (is_cell_flat c) && (is_int_flat l)
    | TidArrRd (tt,i)    -> (is_tidarr_flat tt) && (is_int_flat i)
and is_elem_flat t =
  match t with
      VarElem _         -> true
    | CellData(c)       -> is_cell_flat c
    | HavocSkiplistElem -> true
    | LowestElem        -> true
    | HighestElem       -> true
and is_addr_flat t =
  match t with
      VarAddr _        -> true
    | Null             -> true
    | ArrAt(c,l)       -> (is_cell_flat c) && (is_int_flat l)
    | AddrArrRd (aa,i) -> (is_addrarr_flat aa) && (is_int_flat i)
and is_cell_flat t =
  match t with
      VarCell _           -> true
    | Error               -> true
    | MkCell (e,aa,tt,l)  -> (is_elem_flat e) && (is_addrarr_flat aa) &&
                             (is_tidarr_flat tt) && (is_int_flat l)
    | CellLockAt (c,l,th) -> (is_cell_flat c) && (is_int_flat l) && (is_tid_flat th)
    | CellUnlockAt (c,l)  -> (is_cell_flat c) && (is_int_flat l)
    | CellAt(m,a)         -> (is_mem_flat m) && (is_addr_flat a)
and is_setth_flat t =
  match t with
      VarSetTh _ -> true
    | EmptySetTh -> true
    | SinglTh(k)         -> (is_tid_flat k)
    | UnionTh(st1,st2)   -> (is_setth_flat st1) && (is_setth_flat st2)
    | IntrTh(st1,st2)    -> (is_setth_flat st1) && (is_setth_flat st2)
    | SetdiffTh(st1,st2) -> (is_setth_flat st1) && (is_setth_flat st2)
and is_setelem_flat t =
  match t with
      VarSetElem _ -> true
    | EmptySetElem -> true
    | SinglElem(k)         -> (is_elem_flat k)
    | UnionElem(st1,st2)   -> (is_setelem_flat st1) && (is_setelem_flat st2)
    | IntrElem(st1,st2)    -> (is_setelem_flat st1) && (is_setelem_flat st2)
    | SetToElems(s,m)      -> (is_set_flat s) && (is_mem_flat m)
    | SetdiffElem(st1,st2) -> (is_setelem_flat st1) && (is_setelem_flat st2)
and is_path_flat t =
  match t with
      VarPath _          -> true
    | Epsilon            -> true
    | SimplePath(a)      -> is_addr_flat a
    | GetPath(m,a1,a2,l) -> (is_mem_flat m) && (is_addr_flat a1) &&
                            (is_addr_flat a2) && (is_int_flat l)
and is_mem_flat t =
  match t with
      VarMem _ -> true
    | Update(m,a,c) -> (is_mem_flat m) && (is_addr_flat a) && (is_cell_flat c)
and is_int_flat t =
  match t with
      IntVal _     -> true
    | VarInt _     -> true
    | IntNeg i     -> is_int_flat i
    | IntAdd (i,j) -> (is_int_flat i) && (is_int_flat j)
    | IntSub (i,j) -> (is_int_flat i) && (is_int_flat j)
    | IntMul (i,j) -> (is_int_flat i) && (is_int_flat j)
    | IntDiv (i,j) -> (is_int_flat i) && (is_int_flat j)
    | CellMax c    -> (is_cell_flat c)
    | HavocLevel   -> true
and is_addrarr_flat t =
  match t with
      VarAddrArray _       -> true
    | AddrArrayUp (aa,i,a) -> (is_addrarr_flat aa) && (is_int_flat i) &&
                              (is_addr_flat a)
    | CellArr c            -> (is_cell_flat c)

and is_tidarr_flat t =
  match t with
      VarTidArray _       -> true
    | TidArrayUp (tt,i,t) -> (is_tidarr_flat tt) && (is_int_flat i) &&
                             (is_tid_flat t)
    | CellTids c          -> (is_cell_flat c)

let is_atom_flat (a:atom) : bool =
  match a with
  | Append(p1,p2,p3)         -> (is_path_flat p1) && (is_path_flat p2) &&
                                (is_path_flat p3)
  | Reach(m,a1,a2,l,p)       -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2) && (is_int_flat l) &&
                                (is_path_flat p)
  | OrderList(m,a1,a2)       -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2)
  | Skiplist(m,s,l,a1,a2,es) -> (is_mem_flat m) &&
                                (is_set_flat s) && (is_int_flat l) &&
                                (is_addr_flat a1) && (is_addr_flat a2) &&
                                (is_setelem_flat es)
  | In(a,s)                  -> (is_addr_flat a) && (is_set_flat s)
  | SubsetEq(s1,s2)          -> (is_set_flat s1) && (is_set_flat s2)
  | InTh(k,st)               -> (is_tid_flat k) && (is_setth_flat st)
  | SubsetEqTh(st1,st2)      -> (is_setth_flat st1) && (is_setth_flat st2)
  | InElem(e,se)             -> (is_elem_flat e) && (is_setelem_flat se)
  | SubsetEqElem(se1,se2)    -> (is_setelem_flat se1) && (is_setelem_flat se2)
  | Less (i1,i2)             -> (is_int_flat i1) && (is_int_flat i2)
  | Greater (i1,i2)          -> (is_int_flat i1) && (is_int_flat i2)
  | LessEq (i1,i2)           -> (is_int_flat i1) && (is_int_flat i2)
  | GreaterEq (i1,i2)        -> (is_int_flat i1) && (is_int_flat i2)
  | LessElem(e1,e2)          -> (is_elem_flat e1) && (is_elem_flat e2)
  | GreaterElem(e1,e2)       -> (is_elem_flat e1) && (is_elem_flat e2)
  | Eq(t1,t2)                -> (is_term_flat t1) && (is_term_flat t2)
  | InEq(x,y)                -> (is_term_flat x) && (is_term_flat y)
  | BoolVar _                -> true
  | PC _                     -> true
  | PCUpdate _               -> true
  | PCRange _                -> true

    
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
    | EmptySet            -> "empty"
    | Singl(addr)         -> Printf.sprintf "{ %s }" (addr_to_str addr)
    | Union(s1,s2)        -> Printf.sprintf "union(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | Intr(s1,s2)         -> Printf.sprintf "intr(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | Setdiff(s1,s2)      -> Printf.sprintf "diff(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | PathToSet(path)     -> Printf.sprintf "path2set(%s)"
                              (path_to_str path)
    | AddrToSet(mem,a,l)  -> Printf.sprintf "addr2set(%s,%s,%s)"
                              (mem_to_str mem) (addr_to_str a)
                              (int_to_str l)
and setth_to_str e =
  match e with
      VarSetTh(v)  -> V.to_str v
    | EmptySetTh  -> "tempty"
    | SinglTh(th) -> Printf.sprintf "[ %s ]" (tid_to_str th)
    | UnionTh(s_1,s_2) -> Printf.sprintf "tunion(%s,%s)"
                            (setth_to_str s_1) (setth_to_str s_2)
    | IntrTh(s_1,s_2) -> Printf.sprintf "tintr(%s,%s)"
                            (setth_to_str s_1) (setth_to_str s_2)
    | SetdiffTh(s_1,s_2) -> Printf.sprintf "tdiff(%s,%s)"
                            (setth_to_str s_1) (setth_to_str s_2)
and setelem_to_str e =
  match e with
      VarSetElem(v)  -> V.to_str v
    | EmptySetElem  -> "eempty"
    | SinglElem(e) -> Printf.sprintf "[ %s ]" (elem_to_str e)
    | UnionElem(s_1,s_2) -> Printf.sprintf "eunion(%s,%s)"
                            (setelem_to_str s_1) (setelem_to_str s_2)
    | IntrElem(s_1,s_2) -> Printf.sprintf "eintr(%s,%s)"
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
  Formula.literal_to_str atom_to_str l

let conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  Formula.conjunctive_formula_to_str atom_to_str cf

let disjunctive_formula_to_str (df:disjunctive_formula) : string =
  Formula.disjunctive_formula_to_str atom_to_str df

let formula_to_str (phi:formula) : string =
  Formula.formula_to_str atom_to_str phi


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
let (@@) = ThreadSet.union

let rec get_tid_in (v:V.t) : ThreadSet.t =
  match V.parameter v with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


and voc_term (expr:term) : ThreadSet.t =
  match expr with
    | VarT v             -> (match V.sort v with
                            | Tid -> ThreadSet.singleton (VarTh v)
                            | _   -> ThreadSet.empty) @@ get_tid_in v
    | SetT(set)          -> voc_set set
    | AddrT(addr)        -> voc_addr addr
    | ElemT(elem)        -> voc_elem elem
    | TidT(th)           -> voc_tid th
    | CellT(cell)        -> voc_cell cell
    | SetThT(setth)      -> voc_setth setth
    | SetElemT(setelem)  -> voc_setelem setelem
    | PathT(path)        -> voc_path path
    | MemT(mem)          -> voc_mem mem
    | IntT(i)            -> voc_int i
    | AddrArrayT(aa)     -> voc_addrarr aa
    | TidArrayT(tt)      -> voc_tidarr tt
    | VarUpdate (v,th,t) -> (get_tid_in v) @@ (voc_tid th) @@ (voc_term t)


and voc_set (e:set) : ThreadSet.t =
  match e with
    VarSet v           -> get_tid_in v
  | EmptySet           -> ThreadSet.empty
  | Singl(addr)        -> (voc_addr addr)
  | Union(s1,s2)       -> (voc_set s1) @@ (voc_set s2)
  | Intr(s1,s2)        -> (voc_set s1) @@ (voc_set s2)
  | Setdiff(s1,s2)     -> (voc_set s1) @@ (voc_set s2)
  | PathToSet(path)    -> (voc_path path)
  | AddrToSet(mem,a,l) -> (voc_mem mem) @@ (voc_addr a) @@ (voc_int l)


and voc_addr (a:addr) : ThreadSet.t =
  match a with
    VarAddr v             -> get_tid_in v
  | Null                  -> ThreadSet.empty
  | ArrAt(cell,l)         -> (voc_cell cell) @@ (voc_int l)
  | AddrArrRd (aa,i)      -> (voc_addrarr aa) @@ (voc_int i)


and voc_elem (e:elem) : ThreadSet.t =
  match e with
    VarElem v          -> get_tid_in v
  | CellData(cell)     -> (voc_cell cell)
  | HavocSkiplistElem  -> ThreadSet.empty
  | LowestElem         -> ThreadSet.empty
  | HighestElem        -> ThreadSet.empty


and voc_tid (th:tid) : ThreadSet.t =
  match th with
    VarTh v              -> ThreadSet.add th (get_tid_in v)
  | NoTid                -> ThreadSet.empty
  | CellLockIdAt(cell,l) -> (voc_cell cell) @@ (voc_int l)
  | TidArrRd (tt,i)      -> (voc_tidarr tt) @@ (voc_int i)


and voc_cell (c:cell) : ThreadSet.t =
  match c with
    VarCell v            -> get_tid_in v
  | Error                -> ThreadSet.empty
  | MkCell(data,aa,tt,l) -> (voc_elem data)  @@
                            (voc_addrarr aa) @@
                            (voc_tidarr tt)  @@
                            (voc_int l)
  | CellLockAt(cell,l,th)-> (voc_cell cell) @@ (voc_int l) @@ (voc_tid th)
  | CellUnlockAt(cell,l) -> (voc_cell cell) @@ (voc_int l)
  | CellAt(mem,addr)     -> (voc_mem mem) @@ (voc_addr addr)


and voc_setth (s:setth) : ThreadSet.t =
  match s with
    VarSetTh v          -> get_tid_in v
  | EmptySetTh          -> ThreadSet.empty
  | SinglTh(th)         -> (voc_tid th)
  | UnionTh(s1,s2)      -> (voc_setth s1) @@ (voc_setth s2)
  | IntrTh(s1,s2)       -> (voc_setth s1) @@ (voc_setth s2)
  | SetdiffTh(s1,s2)    -> (voc_setth s1) @@ (voc_setth s2)


and voc_setelem (s:setelem) : ThreadSet.t =
  match s with
    VarSetElem v          -> get_tid_in v
  | EmptySetElem          -> ThreadSet.empty
  | SinglElem(e)          -> (voc_elem e)
  | UnionElem(s1,s2)      -> (voc_setelem s1) @@ (voc_setelem s2)
  | IntrElem(s1,s2)       -> (voc_setelem s1) @@ (voc_setelem s2)
  | SetdiffElem(s1,s2)    -> (voc_setelem s1) @@ (voc_setelem s2)
  | SetToElems(s,m)       -> (voc_set s) @@ (voc_mem m)


and voc_path (p:path) : ThreadSet.t =
  match p with
    VarPath v                  -> get_tid_in v
  | Epsilon                    -> ThreadSet.empty
  | SimplePath(addr)           -> (voc_addr addr)
  | GetPath(mem,a_from,a_to,l) -> (voc_mem mem) @@
                                  (voc_addr a_from) @@
                                  (voc_addr a_to)   @@
                                  (voc_int l)


and voc_mem (m:mem) : ThreadSet.t =
  match m with
    VarMem v             -> get_tid_in v
  | Update(mem,add,cell) -> (voc_mem mem) @@ (voc_addr add) @@ (voc_cell cell)


and voc_int (i:integer) : ThreadSet.t =
  match i with
    IntVal _       -> ThreadSet.empty
  | VarInt v       -> get_tid_in v
  | IntNeg i       -> voc_int i
  | IntAdd (i1,i2) -> (voc_int i1) @@ (voc_int i2)
  | IntSub (i1,i2) -> (voc_int i1) @@ (voc_int i2)
  | IntMul (i1,i2) -> (voc_int i1) @@ (voc_int i2)
  | IntDiv (i1,i2) -> (voc_int i1) @@ (voc_int i2)
  | CellMax c      -> (voc_cell c)
  | HavocLevel     -> ThreadSet.empty


and voc_addrarr (arr:addrarr) : ThreadSet.t =
  match arr with
    VarAddrArray v       -> get_tid_in v
  | AddrArrayUp (aa,i,a) -> (voc_addrarr aa) @@ (voc_int i) @@ (voc_addr a)
  | CellArr c            -> (voc_cell c)


and voc_tidarr (arr:tidarr) : ThreadSet.t =
  match arr with
    VarTidArray v       -> get_tid_in v
  | TidArrayUp (tt,i,t) -> (voc_tidarr tt) @@ (voc_int i) @@ (voc_tid t)
  | CellTids c          -> (voc_cell c)


and voc_atom (a:atom) : ThreadSet.t =
  match a with
    Append(p1,p2,pres)                 -> (voc_path p1) @@
                                          (voc_path p2) @@
                                          (voc_path pres)
  | Reach(h,a_from,a_to,l,p)           -> (voc_mem h) @@
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
  | InElem(e,s)                        -> (voc_elem e) @@ (voc_setelem s)
  | SubsetEqElem(s_in,s_out)           -> (voc_setelem s_in) @@ (voc_setelem s_out)
  | Less (i1,i2)                       -> (voc_int i1) @@ (voc_int i2)
  | Greater (i1,i2)                    -> (voc_int i1) @@ (voc_int i2)
  | LessEq (i1,i2)                     -> (voc_int i1) @@ (voc_int i2)
  | GreaterEq (i1,i2)                  -> (voc_int i1) @@ (voc_int i2)
  | LessElem(e1,e2)                    -> (voc_elem e1) @@ (voc_elem e2)
  | GreaterElem(e1,e2)                 -> (voc_elem e1) @@ (voc_elem e2)
  | Eq(exp)                            -> (voc_eq exp)
  | InEq(exp)                          -> (voc_ineq exp)
  | BoolVar v                          -> get_tid_in v
  | PC (_,t,_)                         -> (match t with
                                           | V.Shared -> ThreadSet.empty
                                           | V.Local x -> ThreadSet.singleton (VarTh x))
  | PCUpdate (_,t)                     -> ThreadSet.singleton t
  | PCRange (_,_,t,_)                  -> (match t with
                                           | V.Shared -> ThreadSet.empty
                                           | V.Local x -> ThreadSet.singleton (VarTh x))


and voc_eq ((t1,t2):eq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


and voc_ineq ((t1,t2):diseq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


let voc_fs = Formula.make_fold
               Formula.GenericLiteralFold
               (fun _ a -> voc_atom a)
               (fun _ -> ThreadSet.empty)
               (@@)

let voc_literal (l:literal) : ThreadSet.t =
  Formula.literal_fold voc_fs () l

let voc_conjunctive_formula (cf:conjunctive_formula) : ThreadSet.t =
  Formula.conjunctive_formula_fold voc_fs () cf

let voc_formula (phi:formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi


let voc (phi:formula) : ThreadSet.t =
  voc_formula phi


let unprimed_voc (phi:formula) : ThreadSet.t =
  ThreadSet.filter (is_primed_tid>>not) (voc phi)


let required_sorts (phi:formula) : sort list =
  let empty = SortSet.empty in
  let union = SortSet.union in
  let add = SortSet.add in
  let single = SortSet.singleton in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in
  let rec req_fs () = Formula.make_fold
                        Formula.GenericLiteralFold
                        (fun _ a -> req_atom a)
                        (fun _ -> empty)
                        (union)

  and req_f (phi:formula) : SortSet.t =
    Formula.formula_fold (req_fs()) () phi

  and req_atom (a:atom) : SortSet.t =
    match a with
    | Append (p1,p2,p3)          -> list_union [req_p p1;req_p p1;req_p p2;req_p p3]
    | Reach (m,a1,a2,l,p)        -> list_union [req_m m;req_a a1;req_a a2;
                                                req_i l;req_p p]
    | OrderList (m,a1,a2)        -> list_union [req_m m;req_a a1;req_a a2]
    | Skiplist (m,s,l,a1,a2,es)  -> list_union [req_m m;req_s s;req_i l;
                                                req_a a1;req_a a2; req_se es]
    | In (a,s)                   -> list_union [req_a a;req_s s]
    | SubsetEq (s1,s2)           -> list_union [req_s s1;req_s s2]
    | InTh (t,s)                 -> list_union [req_t t;req_st s]
    | SubsetEqTh (s1,s2)         -> list_union [req_st s1;req_st s2]
    | InElem (e,s)               -> list_union [req_e e;req_se s]
    | SubsetEqElem (s1,s2)       -> list_union [req_se s1;req_se s2]
    | Less (i1,i2)               -> list_union [req_i i1;req_i i2]
    | Greater (i1,i2)            -> list_union [req_i i1;req_i i2]
    | LessEq (i1,i2)             -> list_union [req_i i1;req_i i2]
    | GreaterEq (i1,i2)          -> list_union [req_i i1;req_i i2]
    | LessElem  (e1,e2)          -> list_union [req_e e1; req_e e2]
    | GreaterElem (e1,e2)        -> list_union [req_e e1; req_e e2]
    | Eq (t1,t2)                 -> union (req_term t1) (req_term t2)
    | InEq (t1,t2)               -> union (req_term t1) (req_term t2)
    | BoolVar _                  -> single Bool
    | PC _                       -> empty
    | PCUpdate _                 -> empty
    | PCRange _                  -> empty

  and req_m (m:mem) : SortSet.t =
    match m with
    | VarMem _         -> single Mem
    | Update (m,a,c)   -> append Mem [req_m m;req_a a;req_c c]

  and req_i (i:integer) : SortSet.t =
    match i with
    | IntVal _           -> single Int
    | VarInt _           -> single Int
    | IntNeg i           -> append Int [req_i i]
    | IntAdd (i1,i2)     -> append Int [req_i i1;req_i i2]
    | IntSub (i1,i2)     -> append Int [req_i i1;req_i i2]
    | IntMul (i1,i2)     -> append Int [req_i i1;req_i i2]
    | IntDiv (i1,i2)     -> append Int [req_i i1;req_i i2]
    | CellMax c          -> append Int [req_c c]
    | HavocLevel         -> empty

  and req_aa (arr:addrarr) : SortSet.t =
    match arr with
    | VarAddrArray _       -> single AddrArray
    | AddrArrayUp (aa,i,a) -> append AddrArray [req_aa aa;req_i i;req_a a]
    | CellArr c            -> append AddrArray [req_c c]

  and req_tt (arr:tidarr) : SortSet.t =
    match arr with
    | VarTidArray _       -> single TidArray
    | TidArrayUp (tt,i,t) -> append TidArray [req_tt tt;req_i i;req_t t]
    | CellTids c          -> append TidArray [req_c c]

  and req_p (p:path) : SortSet.t =
    match p with
    | VarPath _           -> single Path
    | Epsilon             -> single Path
    | SimplePath a        -> append Path [req_a a]
    | GetPath (m,a1,a2,l) -> append Path [req_m m;req_a a1;req_a a2;req_i l]

  and req_st (s:setth) : SortSet.t =
    match s with
    | VarSetTh _         -> single SetTh
    | EmptySetTh         -> single SetTh
    | SinglTh t          -> append SetTh [req_t t]
    | UnionTh (s1,s2)    -> append SetTh [req_st s1;req_st s2]
    | IntrTh (s1,s2)     -> append SetTh [req_st s1;req_st s2]
    | SetdiffTh (s1,s2)  -> append SetTh [req_st s1;req_st s2]

  and req_se (s:setelem) : SortSet.t =
    match s with
    | VarSetElem _         -> single SetElem
    | EmptySetElem         -> single SetElem
    | SinglElem e          -> append SetElem [req_e e]
    | UnionElem (s1,s2)    -> append SetElem [req_se s1;req_se s2]
    | IntrElem (s1,s2)     -> append SetElem [req_se s1;req_se s2]
    | SetToElems (s,m)     -> append SetElem [req_s   s;req_m   m]
    | SetdiffElem (s1,s2)  -> append SetElem [req_se s1;req_se s2]

  and req_c (c:cell) : SortSet.t =
    match c with
    | VarCell _          -> single Cell
    | Error              -> single Cell
    | MkCell (e,aa,tt,l) -> append Cell [req_e e;req_aa aa; req_tt tt;req_i l]
    | CellLockAt (c,l,t) -> append Cell [req_c c;req_i l;req_t t]
    | CellUnlockAt (c,l) -> append Cell [req_c c;req_i l]
    | CellAt (m,a)       -> append Cell [req_m m;req_a a]

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _         -> single Addr
    | Null              -> single Addr
    | ArrAt (c,l)      -> append Addr [req_c c;req_i l]
    | AddrArrRd (aa,i)  -> append Addr [req_aa aa;req_i i]

  and req_e (e:elem) : SortSet.t =
    match e with
    | VarElem _         -> single Elem
    | CellData c        -> append Elem [req_c c]
    | HavocSkiplistElem -> single Elem
    | LowestElem        -> single Elem
    | HighestElem       -> single Elem

  and req_t (t:tid) : SortSet.t =
    match t with
    | VarTh _            -> single Tid
    | NoTid             -> single Tid
    | CellLockIdAt (c,l) -> append Tid [req_c c;req_i l]
    | TidArrRd (tt,i)   -> append Tid [req_tt tt;req_i i]

  and req_s (s:set) : SortSet.t =
    match s with
    | VarSet _         -> single Set
    | EmptySet         -> single Set
    | Singl a          -> append Set  [req_a a]
    | Union (s1,s2)    -> append Set [req_s s1;req_s s2]
    | Intr (s1,s2)     -> append Set [req_s s1;req_s s2]
    | Setdiff (s1,s2)  -> append Set [req_s s1;req_s s2]
    | PathToSet p      -> append Set [req_p p]
    | AddrToSet (m,a,l)-> append Set [req_m m;req_a a;req_i l]

  and req_term (t:term) : SortSet.t =
    match t with
    | VarT v                       -> single (V.sort v)
    | SetT s                       -> req_s s
    | ElemT e                      -> req_e e
    | TidT t                      -> req_t t
    | AddrT a                      -> req_a a
    | CellT c                      -> req_c c
    | SetThT s                     -> req_st s
    | SetElemT s                   -> req_se s
    | PathT p                      -> req_p p
    | MemT m                       -> req_m m
    | IntT i                       -> req_i i
    | AddrArrayT aa                -> req_aa aa
    | TidArrayT tt                 -> req_tt tt
    | VarUpdate (v,t,tr)           -> append (V.sort v) [req_t t;req_term tr]
  in
    SortSet.elements (req_f phi)

 

let special_ops (phi:formula) : special_op_t list =
  let empty = OpsSet.empty in
  let union = OpsSet.union in
  let add = OpsSet.add in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in


  let rec ops_fs () = Formula.make_fold
                        Formula.GenericLiteralFold
                        (fun _ a -> ops_atom a)
                        (fun _ -> empty)
                        (union)

  and ops_f (phi:formula) : OpsSet.t =
    Formula.formula_fold (ops_fs()) () phi

  and ops_atom (a:atom) : OpsSet.t =
    match a with
    | Append (p1,p2,p3)          -> list_union [ops_p p1;ops_p p1;ops_p p2;ops_p p3]
    | Reach (m,a1,a2,l,p)        -> append Reachable[ops_m m;ops_a a1;ops_a a2;
                                                     ops_i l;ops_p p]
    | OrderList (m,a1,a2)        -> append OrderedList[ops_m m;ops_a a1;ops_a a2]
    | Skiplist (m,s,l,a1,a2,es)  -> append SkiplistProp[ops_m m;ops_s s; ops_i l;
                                                        ops_a a1;ops_a a2; ops_se es]
    | In (a,s)                   -> list_union [ops_a a;ops_s s]
    | SubsetEq (s1,s2)           -> list_union [ops_s s1;ops_s s2]
    | InTh (t,s)                 -> list_union [ops_t t;ops_st s]
    | SubsetEqTh (s1,s2)         -> list_union [ops_st s1;ops_st s2]
    | InElem (e,s)               -> list_union [ops_e e;ops_se s]
    | SubsetEqElem (s1,s2)       -> list_union [ops_se s1;ops_se s2]
    | Less (i1,i2)               -> list_union [ops_i i1;ops_i i2]
    | Greater (i1,i2)            -> list_union [ops_i i1;ops_i i2]
    | LessEq (i1,i2)             -> list_union [ops_i i1;ops_i i2]
    | GreaterEq (i1,i2)          -> list_union [ops_i i1;ops_i i2]
    | LessElem (e1,e2)           -> append ElemOrder [ops_e e1; ops_e e2]
    | GreaterElem (e1,e2)        -> append ElemOrder [ops_e e1; ops_e e2]
    | Eq (t1,t2)                 -> list_union [ops_term t1;ops_term t2]
    | InEq (t1,t2)               -> list_union [ops_term t1;ops_term t2]
    | BoolVar _                  -> empty
    | PC _                       -> empty
    | PCUpdate _                 -> empty
    | PCRange _                  -> empty

  and ops_m (m:mem) : OpsSet.t =
    match m with
    | VarMem _         -> empty
    | Update (m,a,c)   -> list_union [ops_m m;ops_a a;ops_c c]

  and ops_i (i:integer) : OpsSet.t =
    match i with
    | IntVal _       -> empty
    | VarInt _       -> empty
    | IntNeg i       -> list_union [ops_i i]
    | IntAdd (i1,i2) -> list_union [ops_i i1; ops_i i2]
    | IntSub (i1,i2) -> list_union [ops_i i1; ops_i i2]
    | IntMul (i1,i2) -> list_union [ops_i i1; ops_i i2]
    | IntDiv (i1,i2) -> list_union [ops_i i1; ops_i i2]
    | CellMax c      -> list_union [ops_c c]
    | HavocLevel     -> empty

  and ops_aa (arr:addrarr) : OpsSet.t =
    match arr with
    | VarAddrArray _       -> empty
    | AddrArrayUp (aa,i,a) -> list_union [ops_aa aa; ops_i i; ops_a a]
    | CellArr c            -> list_union [ops_c c]

  and ops_tt (arr:tidarr) : OpsSet.t =
    match arr with
    | VarTidArray _       -> empty
    | TidArrayUp (tt,i,t) -> list_union [ops_tt tt; ops_i i; ops_t t]
    | CellTids c          -> list_union [ops_c c]

  and ops_p (p:path) : OpsSet.t =
    match p with
    | VarPath _           -> empty
    | Epsilon             -> empty
    | SimplePath a        -> ops_a a
    | GetPath (m,a1,a2,l) -> append Getp [ops_m m;ops_a a1;ops_a a2;ops_i l]

  and ops_st (s:setth) : OpsSet.t =
    match s with
    | VarSetTh _         -> empty
    | EmptySetTh         -> empty
    | SinglTh t          -> ops_t t
    | UnionTh (s1,s2)    -> list_union [ops_st s1;ops_st s2]
    | IntrTh (s1,s2)     -> list_union [ops_st s1;ops_st s2]
    | SetdiffTh (s1,s2)  -> list_union [ops_st s1;ops_st s2]

  and ops_se (s:setelem) : OpsSet.t =
    match s with
    | VarSetElem _         -> empty
    | EmptySetElem         -> empty
    | SinglElem e          -> ops_e e
    | UnionElem (s1,s2)    -> list_union [ops_se s1;ops_se s2]
    | IntrElem (s1,s2)     -> list_union [ops_se s1;ops_se s2]
    | SetToElems(s,m)      -> append Set2Elem [ops_s s;ops_m m]
    | SetdiffElem (s1,s2)  -> list_union [ops_se s1;ops_se s2]

  and ops_c (c:cell) : OpsSet.t =
    match c with
    | VarCell _          -> empty
    | Error              -> empty
    | MkCell (e,aa,tt,l) -> list_union [ops_e e;ops_aa aa;ops_tt tt;ops_i l]
    | CellLockAt (c,l,t) -> list_union [ops_c c;ops_i l;ops_t t]
    | CellUnlockAt (c,l) -> list_union [ops_c c;ops_i l]
    | CellAt (m,a)       -> list_union [ops_m m;ops_a a]

  and ops_a (a:addr) : OpsSet.t =
    match a with
    | VarAddr _            -> empty
    | Null                 -> empty
    | ArrAt (c,l)         -> list_union [ops_c c;ops_i l]
    | AddrArrRd (aa,i)     -> list_union [ops_aa aa;ops_i i]

  and ops_e (e:elem) : OpsSet.t =
    match e with
    | VarElem _         -> empty
    | CellData c        -> ops_c c
    | HavocSkiplistElem -> empty
    | LowestElem        -> empty
    | HighestElem       -> empty

  and ops_t (t:tid) : OpsSet.t =
    match t with
    | VarTh _            -> empty
    | NoTid             -> empty
    | CellLockIdAt (c,l) -> list_union [ops_c c;ops_i l]
    | TidArrRd (tt,i)   -> list_union [ops_tt tt;ops_i i]

  and ops_s (s:set) : OpsSet.t =
    match s with
    | VarSet _          -> empty
    | EmptySet          -> empty
    | Singl a           -> ops_a a
    | Union (s1,s2)     -> list_union [ops_s s1;ops_s s2]
    | Intr (s1,s2)      -> list_union [ops_s s1;ops_s s2]
    | Setdiff (s1,s2)   -> list_union [ops_s s1;ops_s s2]
    | PathToSet p       -> append Path2Set [ops_p p]
    | AddrToSet (m,a,l) -> append Addr2Set [ops_m m;ops_a a;ops_i l]

  and ops_term (t:term) : OpsSet.t =
    match t with
    | VarT _             -> empty
    | SetT s             -> ops_s s
    | ElemT e            -> ops_e e
    | TidT t            -> ops_t t
    | AddrT a            -> ops_a a
    | CellT c            -> ops_c c
    | SetThT s           -> ops_st s
    | SetElemT s         -> ops_se s
    | PathT p            -> ops_p p
    | MemT m             -> ops_m m
    | IntT i             -> ops_i i
    | AddrArrayT aa      -> ops_aa aa
    | TidArrayT tt       -> ops_tt tt
    | VarUpdate (_,t,tr) -> list_union [ops_t t;ops_term tr]
  in
    OpsSet.elements (ops_f phi)


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



(*
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
*)


(* Normalization *)


(*
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
  V.gen_fresh_var sort_to_str {treat_as_pc=false;} gen s
*)


(*


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

  *)


let make_compatible_term_from_var (t:term) (v:V.t) : term =
  match t with
  | VarT _       -> VarT v
  | SetT _       -> SetT       (VarSet v)
  | ElemT _      -> ElemT      (VarElem v)
  | TidT _       -> TidT       (VarTh v)
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




module NOpt = struct
                module VS = V
                type norm_atom = atom
                type norm_term = term
                type norm_formula = formula
                let norm_varset = varset
                let norm_fresh_vinfo = (fun _ -> {treat_as_pc=false})
                let norm_fresh_vname = sort_to_str
              end

module TSLNorm = Normalization.Make(NOpt)


let rec norm_literal (info:TSLNorm.t) (l:literal) : formula =
  let append_if_diff (t:term) (v:V.t) : unit =
    if is_var_term t then
      (*(if (term_to_var t) <> v then Hashtbl.add info.term_map t v)*)
      (if (term_to_var t) <> v then TSLNorm.add_term_map info t v)
    else
      TSLNorm.add_term_map info t v in
(*      Hashtbl.add info.term_map t v in *)
  let gen_if_not_var (t:term) (s:sort) : V.t =
    let _ = verbl _LONG_INFO "GEN_IF_NOT_VAR FOR TERM: %s\n" (term_to_str t) in
    if is_var_term t then (verbl _LONG_INFO "WAS A VARIABLE\n"; term_to_var t)
    else try
           verbl _LONG_INFO "EXISTING PAIRS:\n";
           TSLNorm.iter_term_map (fun t v ->
             verbl _LONG_INFO "%s ----> %s\n" (term_to_str t) (V.to_str v)
           ) info;
           try
             (*Hashtbl.find info.processed_term_map t*)
             TSLNorm.find_proc_term info t
(*           with _ -> Hashtbl.find info.term_map t*)
           with _ -> TSLNorm.find_term_map info t
         with _ -> begin
                     let v = TSLNorm.gen_fresh_var info s in
(*                     let v = gen_fresh_var info.fresh_gen_info s in*)
                     verbl _LONG_INFO "APPENDING A NEW VARIABLE: %s\n" (V.to_str v);
                     append_if_diff t v; v
                   end in
  let rec norm_set (s:set) : set =
    match s with
    | VarSet v -> VarSet v
    | EmptySet -> EmptySet
    | Singl a -> Singl (norm_addr a)
    | Union (s1,s2) -> Union (norm_set s1, norm_set s2)
    | Intr (s1,s2) -> Intr (norm_set s1, norm_set s2)
    | Setdiff (s1,s2) -> Setdiff (norm_set s1, norm_set s2)
    | PathToSet p -> PathToSet (norm_path p)
    | AddrToSet (m,a,i) -> let i_var = gen_if_not_var (IntT i) Int in
                             AddrToSet (norm_mem m, norm_addr a, VarInt i_var)

  and norm_tid (t:tid) : tid =
    match t with
    | VarTh v -> VarTh v
    | NoTid -> NoTid
    | CellLockIdAt (c,i) -> CellLockIdAt (norm_cell c, norm_int i)
    | TidArrRd _ -> let t_var = gen_if_not_var (TidT t) Tid in
                      VarTh t_var
(*                          TidArrRd (norm_tidarr tt, VarInt i_var) *)

  and norm_elem (e:elem) : elem =
    match e with
    | VarElem v -> VarElem v
    | CellData c -> CellData (norm_cell c)
    | HavocSkiplistElem -> HavocSkiplistElem
    | LowestElem -> LowestElem
    | HighestElem -> HighestElem

  and norm_addr (a:addr) : addr =
    match a with
    | VarAddr v -> VarAddr v
    | Null -> Null
    | ArrAt (c,i) -> let i_var = gen_if_not_var (IntT i) Int in
                        ArrAt (norm_cell c, VarInt i_var)
    | AddrArrRd _ -> let a_var = gen_if_not_var (AddrT a) Addr in
                       VarAddr a_var

  and norm_cell (c:cell) : cell =
    match c with
    | VarCell v -> VarCell v
    | Error -> Error
    | MkCell _ -> let c_var = gen_if_not_var (CellT c) Cell in
                    VarCell c_var
    | CellLockAt (c,i,t) -> let i_var = gen_if_not_var (IntT i) Int in
                              CellLockAt (norm_cell c, VarInt i_var, norm_tid t)
    | CellUnlockAt (c,i) -> let i_var = gen_if_not_var (IntT i) Int in
                              CellUnlockAt (norm_cell c, VarInt i_var)
    | CellAt (m,a) -> CellAt (norm_mem m, norm_addr a)

  and norm_setth (s:setth) : setth =
    match s with
    | VarSetTh v -> VarSetTh v
    | EmptySetTh -> EmptySetTh
    | SinglTh t -> SinglTh (norm_tid t)
    | UnionTh (s1,s2) -> UnionTh (norm_setth s1, norm_setth s2)
    | IntrTh (s1,s2) -> IntrTh (norm_setth s1, norm_setth s2)
    | SetdiffTh (s1,s2) -> SetdiffTh (norm_setth s1, norm_setth s2)

  and norm_setelem (s:setelem) : setelem =
    match s with
    | VarSetElem v -> VarSetElem v
    | EmptySetElem -> EmptySetElem
    | SinglElem e -> SinglElem (norm_elem e)
    | UnionElem (s1,s2) -> UnionElem (norm_setelem s1, norm_setelem s2)
    | IntrElem (s1,s2) -> IntrElem (norm_setelem s1, norm_setelem s2)
    | SetToElems (s,m) -> SetToElems (norm_set s, norm_mem m)
    | SetdiffElem (s1,s2) -> SetdiffElem (norm_setelem s1, norm_setelem s2)

  and norm_path (p:path) : path =
    match p with
    | VarPath v -> VarPath v
    | Epsilon -> Epsilon
    | SimplePath a -> SimplePath (norm_addr a)
    | GetPath (m,a1,a2,i) -> let i_var = gen_if_not_var (IntT i) Int in
                               GetPath (norm_mem m, norm_addr a1,
                                        norm_addr a2, VarInt i_var)

  and norm_mem (m:mem) : mem =
    match m with
    | VarMem v -> VarMem v
    | Update (m,a,c) -> Update (norm_mem m, norm_addr a, norm_cell c)

  and norm_int (i:integer) : integer =
    match i with
    | IntVal _ -> VarInt (gen_if_not_var (IntT i) Int)
    | VarInt v -> VarInt v
    | IntNeg j -> IntNeg j
    | IntAdd (j1,j2) -> IntAdd (j1,j2)
    | IntSub (j1,j2) -> IntSub (j1,j2)
    | IntMul (j1,j2) -> IntMul (j1,j2)
    | IntDiv (j1,j2) -> IntDiv (j1,j2)
    | CellMax _ -> let l = gen_if_not_var (IntT i) Int in
                     VarInt l
    | HavocLevel -> HavocLevel

  and norm_addrarr (aa:addrarr) : addrarr =
    match aa with
    | VarAddrArray v -> VarAddrArray v
    | AddrArrayUp (bb,i,a) -> let i_var = gen_if_not_var (IntT i) Int in
                                AddrArrayUp (norm_addrarr bb, VarInt i_var, norm_addr a)
    | CellArr c -> CellArr (norm_cell c)

  and norm_tidarr (tt:tidarr) : tidarr =
    match tt with
    | VarTidArray v -> VarTidArray v
    | TidArrayUp (yy,i,t) -> let i_var = gen_if_not_var (IntT i) Int in
                                TidArrayUp (norm_tidarr yy, VarInt i_var, norm_tid t)
    | CellTids c -> CellTids (norm_cell c)

  and norm_term (t:term) : term =
    match t with
    | VarT v -> VarT v
    | SetT s -> SetT (norm_set s)
    | ElemT e -> ElemT (norm_elem e)
    | TidT t -> TidT (norm_tid t)
    | AddrT a -> AddrT (norm_addr a)
    | CellT c -> CellT (norm_cell c)
    | SetThT s -> SetThT (norm_setth s)
    | SetElemT s -> SetElemT (norm_setelem s)
    | PathT p -> PathT (norm_path p)
    | MemT m -> MemT (norm_mem m)
    | IntT i -> IntT (norm_int i)
    | AddrArrayT aa -> AddrArrayT (norm_addrarr aa)
    | TidArrayT tt -> TidArrayT (norm_tidarr tt)
    | VarUpdate (v,th,t) -> VarUpdate (v, norm_tid th, norm_term t)


  and norm_atom (a:atom) : atom =
    match a with
    | Append (p1,p2,p3) -> Append (norm_path p1, norm_path p2, norm_path p3)
    | Reach (m,a1,a2,i,p) -> let i_var = gen_if_not_var (IntT i) Int in
                               Reach (norm_mem m, norm_addr a1, norm_addr a2,
                                      VarInt i_var, norm_path p)
    | OrderList (m,a1,a2) -> OrderList (norm_mem m, norm_addr a1, norm_addr a2)
    | Skiplist(m,s,i,a1,a2,es) -> let i_var = gen_if_not_var (IntT i) Int in
                                   Skiplist(norm_mem m, norm_set s, VarInt i_var,
                                            norm_addr a1, norm_addr a2, norm_setelem es)
    | In (a,s) -> In (norm_addr a, norm_set s)
    | SubsetEq (s1,s2) -> SubsetEq (norm_set s1, norm_set s2)
    | InTh (t,s) -> InTh (norm_tid t, norm_setth s)
    | SubsetEqTh (s1,s2) -> SubsetEqTh (norm_setth s1, norm_setth s2)
    | InElem (e,s) -> InElem (norm_elem e, norm_setelem s)
    | SubsetEqElem (s1,s2) -> SubsetEqElem (norm_setelem s1, norm_setelem s2)
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
    | LessElem (e1,e2) -> LessElem (norm_elem e1, norm_elem e2)
    | GreaterElem (e1,e2) -> GreaterElem (norm_elem e1, norm_elem e2)
    (* Equality between cell variable and MkCell *)
    | Eq (CellT (VarCell v), CellT (MkCell (e,aa,tt,i)))
    | Eq (CellT (MkCell (e,aa,tt,i)), CellT (VarCell v)) ->
        let i_var = gen_if_not_var (IntT i) Int in
        let aa_norm = norm_addrarr aa in
        let tt_norm = norm_tidarr tt in
        let aa' = match aa_norm with
                  | AddrArrayUp _ -> VarAddrArray (gen_if_not_var
                                      (AddrArrayT aa_norm) AddrArray)
                  | _ -> aa_norm in
        let tt' = match tt_norm with
                  | TidArrayUp _ -> VarTidArray (gen_if_not_var
                                      (TidArrayT tt_norm) TidArray)
                  | _ -> tt_norm in
          Eq (CellT (VarCell v), CellT (MkCell(norm_elem e, aa',
                                               tt', VarInt i_var)))
    (* Inequality between cell variable and MkCell *)
    | InEq (CellT (VarCell v), CellT (MkCell (e,aa,tt,i)))
    | InEq (CellT (MkCell (e,aa,tt,i)), CellT (VarCell v)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          InEq (CellT (VarCell v), CellT (MkCell(norm_elem e, norm_addrarr aa,
                                                 norm_tidarr tt, VarInt i_var)))
    (* Equality between address variable and address array *)
    | Eq (AddrT (VarAddr a), AddrT (AddrArrRd(aa,i)))
    | Eq (AddrT (AddrArrRd(aa,i)), AddrT (VarAddr a)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          Eq (AddrT (VarAddr a),
              AddrT (AddrArrRd(norm_addrarr aa, VarInt i_var)))
    (* Inequality between address variable and address array *)
    | InEq (AddrT (VarAddr a), AddrT (AddrArrRd(aa,i)))
    | InEq (AddrT (AddrArrRd(aa,i)), AddrT (VarAddr a)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          InEq (AddrT (VarAddr a),
                AddrT (AddrArrRd(norm_addrarr aa,VarInt i_var)))
    (* Equality between tid variable  and tids array *)
    | Eq (TidT (VarTh a), TidT (TidArrRd(tt,i)))
    | Eq (TidT (TidArrRd(tt,i)), TidT (VarTh a)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          Eq (TidT (VarTh a),
              TidT (TidArrRd(norm_tidarr tt, VarInt i_var)))
    (* Inequality between tid variable and tids array *)
    | InEq (TidT (VarTh a), TidT (TidArrRd(tt,i)))
    | InEq (TidT (TidArrRd(tt,i)), TidT (VarTh a)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          InEq (TidT (VarTh a),
                TidT (TidArrRd(norm_tidarr tt, VarInt i_var)))
    (* General equalities and inequalities *)
    | Eq (t1,t2) -> Eq (norm_term t1, norm_term t2)
    | InEq (t1,t2) -> InEq (norm_term t1, norm_term t2)
    | BoolVar v -> BoolVar v
    | PC (i,topt,pr) -> let norm_topt = match topt with
                                        | V.Shared -> V.Shared
(*                                        | V.Local t -> V.Local (norm_tid t) in *)
                                        | V.Local t -> V.Local t in
                        PC (i, norm_topt, pr)
    | PCUpdate (i,t) -> PCUpdate (i, norm_tid t)
    | PCRange (i,j,topt,pr) -> let norm_topt = match topt with
                                              | V.Shared -> V.Shared
(*                                              | V.Local t -> V.Local (norm_tid t) in*)
                                              | V.Local t -> V.Local t in
                               PCRange (i, j, norm_topt, pr)

  in
  match l with
  | F.Atom a -> F.Literal(F.Atom (norm_atom a))
  | F.NegAtom (Skiplist(m,s,i,a1,a2,es)) ->
      let m_var = gen_if_not_var (MemT m) Mem in
      let s_var = gen_if_not_var (SetT s) Set in
      let i_var = gen_if_not_var (IntT i) Int in
      let a1_var = gen_if_not_var (AddrT a1) Addr in
      let a2_var = gen_if_not_var (AddrT a2) Addr in
      let es_var = gen_if_not_var (SetElemT es) SetElem in
      let p = VarPath (TSLNorm.gen_fresh_var info Path) in
      let q = VarPath (TSLNorm.gen_fresh_var info Path) in
      let x = VarSet (TSLNorm.gen_fresh_var info Set) in
      let r = VarSet (TSLNorm.gen_fresh_var info Set) in
      let u = VarSet (TSLNorm.gen_fresh_var info Set) in
      let zero = gen_if_not_var (IntT (IntVal 0)) Int in
      let null = gen_if_not_var (AddrT Null) Addr in
      let a = VarAddr (TSLNorm.gen_fresh_var info Addr) in
      let c = VarCell (TSLNorm.gen_fresh_var info Cell) in
      let e = VarElem (TSLNorm.gen_fresh_var info Elem) in
      let aa = VarAddrArray (TSLNorm.gen_fresh_var info AddrArray) in
      let tt = VarTidArray (TSLNorm.gen_fresh_var info TidArray) in
      let l1 = VarInt (TSLNorm.gen_fresh_var info Int) in
      let l2 = VarInt (TSLNorm.gen_fresh_var info Int) in
      let phi_unordered = norm_literal info (F.NegAtom(OrderList
                            (VarMem m_var,VarAddr a1_var,VarAddr null))) in
      let phi_diff = norm_literal info (F.Atom(InEq(SetT (VarSet s_var), SetT r))) in
(*      let phi_a_in_s = norm_literal info (Atom(In(a,VarSet s_var))) in *)
      let phi_not_elems = norm_literal info (F.Atom(InEq(SetElemT (VarSetElem es_var),
                                                         SetElemT(SetToElems(VarSet s_var,VarMem m_var))))) in
      let phi_not_subset = norm_literal info (F.NegAtom(SubsetEq(u,r))) in
        F.disj_list
          [phi_unordered;
           phi_not_elems;
(*
           F.conj_list [eq_path p (GetPath(VarMem m_var,VarAddr a1_var,VarAddr null,VarInt zero));
                        eq_set r (PathToSet(p));
                        phi_diff];
*)
           F.conj_list [eq_set r (AddrToSet(VarMem m_var, VarAddr a1_var, VarInt zero));
                        phi_diff];
           F.Literal(F.Atom(Less(VarInt i_var, VarInt zero)));
           F.conj_list [ineq_int (VarInt i_var) (VarInt zero);
                        F.Literal(F.Atom(LessEq(VarInt zero,l2)));
                        F.Literal(F.Atom(LessEq(l2,l1)));
                        F.Literal(F.Atom(LessEq(l1, (VarInt i_var))));
                        eq_cell c (CellAt(VarMem m_var,VarAddr a2_var));
                        eq_cell c (MkCell(e,aa,tt,l1));
                        eq_addr a (AddrArrRd(aa,l2));
                        ineq_addr a (VarAddr null)];
           F.conj_list [ineq_int (VarInt i_var) (VarInt zero);
                        F.Literal(F.Atom(LessEq(VarInt zero,l1)));
                        F.Literal(F.Atom(Less(l1,VarInt i_var)));
                        eq_int (l2) (IntAdd(l1,IntVal 1));
                        eq_path (p) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr null,l1));
                        eq_path (q) (GetPath(VarMem m_var,VarAddr a1_var,VarAddr null,l2));
                        eq_set (r) (PathToSet p);
                        eq_set (u) (PathToSet q);
                        phi_not_subset];
           F.conj_list [eq_set (x) (AddrToSet(VarMem m_var,VarAddr a1_var,l1));
                        F.atom_to_formula (LessEq(VarInt zero,l1));
                        F.atom_to_formula (LessEq(l1,VarInt i_var));
                        F.Literal (F.NegAtom (In (VarAddr a2_var, x)))]
          ]
  | F.NegAtom a -> F.Literal(F.NegAtom (norm_atom a))


let rec norm_formula (info:TSLNorm.t) (phi:formula) : formula =
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
    let norm_info = TSLNorm.new_norm phi in
    (* Process the original formula *)
    let phi' = norm_formula norm_info (F.nnf phi) in
    (* Normalize all remaining literals stored in the normalization table *)
    verbl _LONG_INFO "WILL NORMALIZE REMAINING ELEMENTS";
    let lit_list = ref [] in
(*    while (Hashtbl.length norm_info.term_map > 0) do *)
    while (TSLNorm.term_map_size norm_info > 0) do
      TSLNorm.iter_term_map (fun t v ->
(*      Hashtbl.iter (fun t v ->*)
        begin
          match t with
          | IntT (CellMax _) -> ()
          | _ -> begin
                   TSLNorm.add_proc_term_map norm_info t v;
                   (*Hashtbl.add norm_info.processed_term_map t v; *)
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
        TSLNorm.remove_term_map norm_info t
        (*Hashtbl.remove norm_info.term_map t*)
      ) norm_info;
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


and replace_terms_term (tbl:(term,term) Hashtbl.t) (expr:term) : term =
  match expr with
    VarT(v)           -> VarT       (replace_terms_in_vars tbl v)
  | SetT(set)         -> SetT       (replace_terms_set tbl set)
  | AddrT(addr)       -> AddrT      (replace_terms_addr tbl addr)
  | ElemT(elem)       -> ElemT      (replace_terms_elem tbl elem)
  | TidT(th)         -> TidT      (replace_terms_tid tbl th)
  | CellT(cell)       -> CellT      (replace_terms_cell tbl cell)
  | SetThT(setth)     -> SetThT     (replace_terms_setth tbl setth)
  | SetElemT(setelem) -> SetElemT   (replace_terms_setelem tbl setelem)
  | PathT(path)       -> PathT      (replace_terms_path tbl path)
  | MemT(mem)         -> MemT       (replace_terms_mem tbl mem)
  | IntT(i)           -> IntT       (replace_terms_int tbl i)
  | AddrArrayT(arr)   -> AddrArrayT (replace_terms_addrarr tbl arr)
  | TidArrayT(arr)    -> TidArrayT  (replace_terms_tidarr tbl arr)
  | VarUpdate(v,th,t) -> VarUpdate  (replace_terms_in_vars tbl v,
                                     replace_terms_tid tbl th,
                                     replace_terms_term tbl t)


and replace_terms_addrarr (tbl:(term,term) Hashtbl.t) (arr:addrarr) : addrarr =
  try
    match Hashtbl.find tbl (AddrArrayT arr) with | AddrArrayT arr' -> arr' | _ -> assert false
  with _ -> begin
    match arr with
      VarAddrArray v       -> VarAddrArray (replace_terms_in_vars tbl v)
        (*TODO: Fix open array case for array variables *)
    | AddrArrayUp(arr,i,a) -> AddrArrayUp(replace_terms_addrarr tbl arr,
                                          replace_terms_int tbl i,
                                          replace_terms_addr tbl a)
    | CellArr c            -> CellArr (replace_terms_cell tbl c)
  end


and replace_terms_tidarr (tbl:(term,term) Hashtbl.t) (arr:tidarr) : tidarr =
  try
    match Hashtbl.find tbl (TidArrayT arr) with | TidArrayT arr' -> arr' | _ -> assert false
  with _ -> begin
    match arr with
      VarTidArray v       -> VarTidArray (replace_terms_in_vars tbl v)
        (*TODO: Fix open array case for array variables *)
    | TidArrayUp(arr,i,t) -> TidArrayUp(replace_terms_tidarr tbl arr,
                                        replace_terms_int tbl i,
                                        replace_terms_tid tbl t)
    | CellTids c            -> CellTids (replace_terms_cell tbl c)
  end


and replace_terms_set (tbl:(term,term) Hashtbl.t) (e:set) : set =
  try
    match Hashtbl.find tbl (SetT e) with | SetT e' -> e' | _ -> assert false
  with _ -> begin
    match e with
      VarSet v             -> VarSet (replace_terms_in_vars tbl v)
    | EmptySet             -> EmptySet
    | Singl(addr)          -> Singl(replace_terms_addr tbl addr)
    | Union(s1,s2)         -> Union(replace_terms_set tbl s1,
                                    replace_terms_set tbl s2)
    | Intr(s1,s2)          -> Intr(replace_terms_set tbl s1,
                                   replace_terms_set tbl s2)
    | Setdiff(s1,s2)       -> Setdiff(replace_terms_set tbl s1,
                                      replace_terms_set tbl s2)
    | PathToSet(path)      -> PathToSet(replace_terms_path tbl path)
    | AddrToSet(mem,a,l)   -> AddrToSet(replace_terms_mem tbl mem,
                                        replace_terms_addr tbl a,
                                        replace_terms_int tbl l)
  end


and replace_terms_addr (tbl:(term,term) Hashtbl.t) (a:addr) : addr =
  try
    match Hashtbl.find tbl (AddrT a) with | AddrT a' -> a' | _ -> assert false
  with _ -> begin
    match a with
      VarAddr v                 -> VarAddr (replace_terms_in_vars tbl v)
    | Null                      -> Null
    | ArrAt(cell,l)            -> ArrAt(replace_terms_cell tbl cell,
                                          replace_terms_int tbl l)
    | AddrArrRd (aa,i)          -> AddrArrRd (replace_terms_addrarr tbl aa,
                                              replace_terms_int tbl i)
  end


and replace_terms_elem (tbl:(term,term) Hashtbl.t) (e:elem) : elem =
  try
    match Hashtbl.find tbl (ElemT e) with | ElemT e' -> e' | _ -> assert false
  with _ -> begin
    match e with
      VarElem v            -> VarElem (replace_terms_in_vars tbl v)
    | CellData(cell)       -> CellData(replace_terms_cell tbl cell)
    | HavocSkiplistElem    -> HavocSkiplistElem
    | LowestElem           -> LowestElem
    | HighestElem          -> HighestElem
  end


and replace_terms_tid (tbl:(term,term) Hashtbl.t) (th:tid) : tid =
  try
    match Hashtbl.find tbl (TidT th) with | TidT th' -> th' | _ -> assert false
  with _ -> begin
    match th with
      VarTh v              -> VarTh (replace_terms_in_vars tbl v)
    | NoTid               -> NoTid
    | CellLockIdAt(cell,l) -> CellLockIdAt(replace_terms_cell tbl cell,
                                           replace_terms_int tbl l)
    | TidArrRd(arr,l)     -> TidArrRd(replace_terms_tidarr tbl arr,
                                        replace_terms_int tbl l)
  end


and replace_terms_cell (tbl:(term,term) Hashtbl.t) (c:cell) : cell =
  try
    match Hashtbl.find tbl (CellT c) with | CellT c' -> c' | _ -> assert false
  with _ -> begin
    match c with
      VarCell v              -> VarCell (replace_terms_in_vars tbl v)
    | Error                  -> Error
    | MkCell(data,aa,ta,l)   -> MkCell(replace_terms_elem tbl data,
                                       replace_terms_addrarr tbl aa,
                                       replace_terms_tidarr tbl ta,
                                       replace_terms_int tbl l)
    | CellLockAt(cell,l, t)  -> CellLockAt(replace_terms_cell tbl cell,
                                           replace_terms_int tbl l,
                                           replace_terms_tid tbl t)
    | CellUnlockAt(cell,l)   -> CellUnlockAt(replace_terms_cell tbl cell,
                                             replace_terms_int tbl l)
    | CellAt(mem,addr)       -> CellAt(replace_terms_mem tbl mem,
                                       replace_terms_addr tbl addr)
  end


and replace_terms_setth (tbl:(term,term) Hashtbl.t) (s:setth) : setth =
  try
    match Hashtbl.find tbl (SetThT s) with | SetThT s' -> s' | _ -> assert false
  with _ -> begin
    match s with
      VarSetTh v            -> VarSetTh (replace_terms_in_vars tbl v)
    | EmptySetTh            -> EmptySetTh
    | SinglTh(th)           -> SinglTh(replace_terms_tid tbl th)
    | UnionTh(s1,s2)        -> UnionTh(replace_terms_setth tbl s1,
                                       replace_terms_setth tbl s2)
    | IntrTh(s1,s2)         -> IntrTh(replace_terms_setth tbl s1,
                                      replace_terms_setth tbl s2)
    | SetdiffTh(s1,s2)      -> SetdiffTh(replace_terms_setth tbl s1,
                                         replace_terms_setth tbl s2)
  end


and replace_terms_setelem (tbl:(term,term) Hashtbl.t) (s:setelem) : setelem =
  try
    match Hashtbl.find tbl (SetElemT s) with | SetElemT s' -> s' | _ -> assert false
  with _ -> begin
    match s with
      VarSetElem v            -> VarSetElem (replace_terms_in_vars tbl v)
    | EmptySetElem            -> EmptySetElem
    | SinglElem(e)            -> SinglElem(replace_terms_elem tbl e)
    | UnionElem(s1,s2)        -> UnionElem(replace_terms_setelem tbl s1,
                                           replace_terms_setelem tbl s2)
    | IntrElem(s1,s2)         -> IntrElem(replace_terms_setelem tbl s1,
                                          replace_terms_setelem tbl s2)
    | SetdiffElem(s1,s2)      -> SetdiffElem(replace_terms_setelem tbl s1,
                                             replace_terms_setelem tbl s2)
    | SetToElems(s,m)         -> SetToElems(replace_terms_set tbl s, replace_terms_mem tbl m)
  end


and replace_terms_path (tbl:(term,term) Hashtbl.t) (path:path) : path =
  try
    match Hashtbl.find tbl (PathT path) with | PathT p' -> p' | _ -> assert false
  with _ -> begin
    match path with
      VarPath v                        -> VarPath (replace_terms_in_vars tbl v)
    | Epsilon                          -> Epsilon
    | SimplePath(addr)                 -> SimplePath(replace_terms_addr tbl addr)
    | GetPath(mem,add_from,add_to,l)   -> GetPath(replace_terms_mem tbl mem,
                                                  replace_terms_addr tbl add_from,
                                                  replace_terms_addr tbl add_to,
                                                  replace_terms_int tbl l)
  end


and replace_terms_mem (tbl:(term,term) Hashtbl.t) (m:mem) : mem =
  try
    match Hashtbl.find tbl (MemT m) with | MemT m' -> m' | _ -> assert false
  with _ -> begin
    match m with
      VarMem v             -> VarMem (replace_terms_in_vars tbl v)
    | Update(mem,add,cell) -> Update(replace_terms_mem tbl mem,
                                     replace_terms_addr tbl add,
                                     replace_terms_cell tbl cell)
  end


and replace_terms_int (tbl:(term,term) Hashtbl.t) (i:integer) : integer =
  try
    match Hashtbl.find tbl (IntT i) with | IntT j -> j | _ -> assert false
  with _ -> begin
    match i with
      IntVal(i)           -> IntVal(i)
    | VarInt v            -> VarInt (replace_terms_in_vars tbl v)
    | IntNeg(i)           -> IntNeg(replace_terms_int tbl i)
    | IntAdd(i1,i2)       -> IntAdd(replace_terms_int tbl i1,
                                    replace_terms_int tbl i2)
    | IntSub(i1,i2)       -> IntSub(replace_terms_int tbl i1,
                                    replace_terms_int tbl i2)
    | IntMul(i1,i2)       -> IntMul(replace_terms_int tbl i1,
                                    replace_terms_int tbl i2)
    | IntDiv(i1,i2)       -> IntDiv(replace_terms_int tbl i1,
                                    replace_terms_int tbl i2)
    | CellMax(c)          -> CellMax(replace_terms_cell tbl c)
    | HavocLevel          -> HavocLevel
  end


and replace_terms_atom (tbl:(term,term) Hashtbl.t) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)                 -> Append(replace_terms_path tbl p1,
                                                 replace_terms_path tbl p2,
                                                 replace_terms_path tbl pres)
  | Reach(h,a_from,a_to,l,p)           -> Reach(replace_terms_mem tbl h,
                                                replace_terms_addr tbl a_from,
                                                replace_terms_addr tbl a_to,
                                                replace_terms_int tbl l,
                                                replace_terms_path tbl p)
  | OrderList(h,a_from,a_to)           -> OrderList(replace_terms_mem tbl h,
                                                    replace_terms_addr tbl a_from,
                                                    replace_terms_addr tbl a_to)
  | Skiplist(h,s,l,a_from,a_to,elems)  -> Skiplist(replace_terms_mem tbl h,
                                                   replace_terms_set tbl s,
                                                   replace_terms_int tbl l,
                                                   replace_terms_addr tbl a_from,
                                                   replace_terms_addr tbl a_to,
                                                   replace_terms_setelem tbl elems)
  | In(a,s)                            -> In(replace_terms_addr tbl a,
                                             replace_terms_set tbl s)
  | SubsetEq(s_in,s_out)               -> SubsetEq(replace_terms_set tbl s_in,
                                                   replace_terms_set tbl s_out)
  | InTh(th,s)                         -> InTh(replace_terms_tid tbl th,
                                               replace_terms_setth tbl s)
  | SubsetEqTh(s_in,s_out)             -> SubsetEqTh(replace_terms_setth tbl s_in,
                                                     replace_terms_setth tbl s_out)
  | InElem(e,s)                        -> InElem(replace_terms_elem tbl e,
                                                 replace_terms_setelem tbl s)
  | SubsetEqElem(s_in,s_out)           -> SubsetEqElem(replace_terms_setelem tbl s_in,
                                                       replace_terms_setelem tbl s_out)
  | Less(i1,i2)                        -> Less(replace_terms_int tbl i1,
                                               replace_terms_int tbl i2)
  | Greater(i1,i2)                     -> Greater(replace_terms_int tbl i1,
                                                  replace_terms_int tbl i2)
  | LessEq(i1,i2)                      -> LessEq(replace_terms_int tbl i1,
                                                 replace_terms_int tbl i2)
  | GreaterEq(i1,i2)                   -> GreaterEq(replace_terms_int tbl i1,
                                                    replace_terms_int tbl i2)
  | LessElem(e1,e2)                    -> LessElem(replace_terms_elem tbl e1,
                                                   replace_terms_elem tbl e2)
  | GreaterElem(e1,e2)                 -> GreaterElem(replace_terms_elem tbl e1,
                                                      replace_terms_elem tbl e2)
  | Eq(exp)                            -> Eq(replace_terms_eq tbl exp)
  | InEq(exp)                          -> InEq(replace_terms_ineq tbl exp)
  | BoolVar v                          -> BoolVar (replace_terms_in_vars tbl v)
  | PC (pc,th,p)                       -> begin
                                            match th with
                                            | V.Shared  -> PC (pc,th,p)
                                            | V.Local t -> PC (pc, V.Local (replace_terms_in_vars tbl t), p)
                                          end
  | PCUpdate (pc,t)                    -> PCUpdate (pc, replace_terms_tid tbl t)
  | PCRange (pc1,pc2,th,p)             -> begin
                                            match th with
                                            | V.Shared  -> PCRange (pc1,pc2,th,p)
                                            | V.Local t -> PCRange (pc1,pc2,V.Local(replace_terms_in_vars tbl t),p)
                                          end


and replace_terms_eq (tbl:(term,term) Hashtbl.t) ((t1,t2):eq) : eq =
  (replace_terms_term tbl t1, replace_terms_term tbl t2)


and replace_terms_ineq (tbl:(term,term) Hashtbl.t) ((t1,t2):diseq) : diseq =
  (replace_terms_term tbl t1, replace_terms_term tbl t2)


let replace_fs = Formula.make_trans
                   Formula.GenericLiteralTrans
                   (fun info a -> replace_terms_atom info a)

let replace_terms_literal (tbl:(term,term) Hashtbl.t) (l:literal) : literal =
  Formula.literal_trans replace_fs tbl l

let replace_terms_formula_aux (tbl:(term,term) Hashtbl.t) (phi:formula) : formula =
  Formula.formula_trans replace_fs tbl phi


let replace_terms (tbl:(term, term) Hashtbl.t) (phi:formula) : formula =
  check_well_defined_replace_table tbl;
  replace_terms_formula_aux tbl phi


(* Vocabulary to variable conversion *)
let voc_to_var (t:tid) : V.t =
  match t with
  | VarTh v -> v
  | _ -> raise(Not_tid_var t)

