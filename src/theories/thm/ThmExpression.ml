open Printf
open LeapLib
open LeapVerbose

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
  | TidArray
  | BucketArray
  | Bool
  | Mark
  | Bucket
  | Lock
  | LockArray
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
    VarT         of V.t
  | SetT         of set
  | ElemT        of elem
  | TidT         of tid
  | AddrT        of addr
  | CellT        of cell
  | SetThT       of setth
  | SetElemT     of setelem
  | PathT        of path
  | MemT         of mem
  | IntT         of integer
  | TidArrayT    of tidarr
  | BucketArrayT of bucketarr
  | MarkT        of mark
  | BucketT      of bucket
  | LockT        of lock
  | LockArrayT   of lockarr
  | VarUpdate    of V.t * tid * term
and eq = term * term
and diseq = term * term
and bucketarr =
  | VarBucketArray of V.t
  | BucketArrayUp  of bucketarr * integer * bucket
and integer =
    IntVal        of int
  | VarInt        of V.t
  | IntNeg        of integer
  | IntAdd        of integer * integer
  | IntSub        of integer * integer
  | IntMul        of integer * integer
  | IntDiv        of integer * integer
  | IntMod        of integer * integer
  | HashCode      of elem
and tidarr =
  | VarTidArray   of V.t
  | TidArrayUp    of tidarr * integer * tid
and set =
    VarSet of V.t
  | EmptySet
  | Singl        of addr
  | Union        of set * set
  | Intr         of set * set
  | Setdiff      of set * set
  | PathToSet    of path
  | AddrToSet    of mem * addr
  | BucketRegion of bucket
and tid =
    VarTh        of V.t
  | NoTid
  | CellLockId   of cell
  | BucketTid    of bucket
  | TidArrRd     of tidarr * integer
  | LockId       of lock
and lock =
    VarLock       of V.t
  | MkLock        of tid
  | LLock         of lock * tid
  | LUnlock       of lock
  | LockArrRd     of lockarr * integer
and lockarr =
  | VarLockArray  of V.t
  | LockArrayUp   of lockarr * integer * lock
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
  | LastLocked of mem * path
(*  | Malloc of elem * addr * tid *)
  | BucketInit of bucket
  | BucketEnd of bucket
and cell =
    VarCell of V.t
  | Error
  | MkCell of elem * addr * tid
  | MkCellMark of elem * addr * tid * mark
  | CellLock of cell * tid
  | CellUnlock of cell
  | CellAt of mem * addr
and mark =
    VarMark of V.t
  | MarkTrue
  | MarkFalse
  | Marked of cell
and bucket =
    VarBucket of V.t
  | MkBucket of addr * addr * set * tid
  | BucketArrRd of bucketarr * integer
and setth =
    VarSetTh of V.t
  | EmptySetTh
  | SinglTh   of tid
  | UnionTh   of setth * setth
  | IntrTh    of setth * setth
  | SetdiffTh of setth * setth
  | LockSet   of mem * path
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
  | Update of mem * addr * cell
and atom =
    Append       of path * path * path
  | Reach        of mem * addr * addr * path
  | OrderList    of mem * addr * addr
  | Hashmap      of mem * set * setelem * bucketarr * integer
  | In           of addr * set
  | SubsetEq     of set  * set
  | InTh         of tid * setth
  | SubsetEqTh   of setth * setth
  | InElem       of elem * setelem
  | SubsetEqElem of setelem * setelem
  | Less         of integer * integer
  | Greater      of integer * integer
  | LessEq       of integer * integer
  | GreaterEq    of integer * integer
  | LessElem     of elem * elem
  | GreaterElem  of elem * elem
  | Eq           of eq
  | InEq         of diseq
  | BoolVar      of V.t
  | PC           of int * V.shared_or_local * bool
  | PCUpdate     of int * tid
  | PCRange      of int * int * V.shared_or_local * bool

and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula

type special_op_t =
  | Reachable
  | Addr2Set
  | Path2Set
  | FstLocked
  | LstLocked
  | Getp
  | Set2Elem
  | ElemOrder
  | OrderedList
  | Lockset
  | HashMap

exception WrongType of term
exception Not_tid_var of tid
exception No_variable_term of term



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
  V.build id s pr th p {treat_as_pc= treat_as_pc;} ~fresh:fresh


let treat_as_pc (v:V.t) : bool =
  (V.info v).treat_as_pc


let is_primed_tid (th:tid) : bool =
  match th with
  | VarTh v           -> V.is_primed v
  | NoTid             -> false
  | CellLockId _      -> false
  | BucketTid _       -> false
  | TidArrRd _        -> false
  | LockId _          -> false
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



module TermSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = term
  end )


let (@@) s1 s2 =
  V.VarSet.union s1 s2

let get_varset_from_param (v:V.t) : V.VarSet.t =
  match V.parameter v with
  | V.Local t -> V.VarSet.singleton t
  | _ -> V.VarSet.empty


let rec get_varset_set s =
  match s with
      VarSet v       -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySet       -> V.VarSet.empty
    | Singl(a)       -> get_varset_addr a
    | Union(s1,s2)   -> (get_varset_set s1) @@ (get_varset_set s2)
    | Intr(s1,s2)    -> (get_varset_set s1) @@ (get_varset_set s2)
    | Setdiff(s1,s2) -> (get_varset_set s1) @@ (get_varset_set s2)
    | PathToSet(p)   -> get_varset_path p
    | AddrToSet(m,a) -> (get_varset_mem m) @@ (get_varset_addr a)
    | BucketRegion b -> (get_varset_bucket b)
and get_varset_tidarr tt =
  match tt with
      VarTidArray v -> V.VarSet.singleton v @@ get_varset_from_param v
    | TidArrayUp (tt,i,t) -> (get_varset_tidarr tt) @@ (get_varset_int i) @@
                             (get_varset_tid t)
and get_varset_bucketarr bb =
  match bb with
      VarBucketArray v -> V.VarSet.singleton v @@ get_varset_from_param v
    | BucketArrayUp (bb,i,b) -> (get_varset_bucketarr bb) @@ (get_varset_int i) @@
                                (get_varset_bucket b)
and get_varset_int i =
  match i with
      IntVal _ -> V.VarSet.empty
    | VarInt v -> V.VarSet.singleton v @@ get_varset_from_param v
    | IntNeg j -> get_varset_int j
    | IntAdd (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntSub (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntMul (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntDiv (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntMod (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | HashCode (e)   -> (get_varset_elem e)
and get_varset_tid th =
  match th with
      VarTh v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | NoTid           -> V.VarSet.empty
    | CellLockId c    -> (get_varset_cell c)
    | BucketTid b     -> (get_varset_bucket b)
    | TidArrRd (tt,i) -> (get_varset_tidarr tt) @@ (get_varset_int i)
    | LockId l        -> (get_varset_lock l)
and get_varset_lock x =
  match x with
      VarLock v        -> V.VarSet.singleton v @@ get_varset_from_param v
    | MkLock (t)       -> (get_varset_tid t)
    | LLock (l,t)      -> (get_varset_lock l) @@ (get_varset_tid t)
    | LUnlock (l)      -> (get_varset_lock l)
    | LockArrRd (ll,i) -> (get_varset_lockarr ll) @@ (get_varset_int i)
and get_varset_lockarr ll =
  match ll with
      VarLockArray v       -> V.VarSet.singleton v @@ get_varset_from_param v
    | LockArrayUp (ll,i,l) -> (get_varset_lockarr ll) @@
                              (get_varset_int i) @@
                              (get_varset_lock l)
and get_varset_elem e =
  match e with
      VarElem v     -> V.VarSet.singleton v @@ get_varset_from_param v
    | CellData c    -> get_varset_cell c
    | HavocListElem -> V.VarSet.empty
    | LowestElem    -> V.VarSet.empty
    | HighestElem   -> V.VarSet.empty
and get_varset_addr a =
  match a with
      VarAddr v        -> V.VarSet.singleton v @@ get_varset_from_param v
    | Null             -> V.VarSet.empty
    | Next c           -> get_varset_cell c
    | FirstLocked(m,p) -> (get_varset_mem m) @@ (get_varset_path p)
    | LastLocked(m,p)  -> (get_varset_mem m) @@ (get_varset_path p)
(*    | Malloc(e,a,th)   -> (get_varset_elem e) @@ (get_varset_addr a) @@  (get_varset_tid th) *)
    | BucketInit b     -> (get_varset_bucket b)
    | BucketEnd b      -> (get_varset_bucket b)
and get_varset_cell c = match c with
      VarCell v      -> V.VarSet.singleton v @@ get_varset_from_param v
    | Error          -> V.VarSet.empty
    | MkCell(e,a,th) -> (get_varset_elem e) @@ (get_varset_addr a) @@ (get_varset_tid th)
    | MkCellMark(e,a,th,m) -> (get_varset_elem e) @@ (get_varset_addr a) @@
                              (get_varset_tid th) @@ (get_varset_mark m)
    | CellLock(c,th) ->  (get_varset_cell c) @@ (get_varset_tid th)
    | CellUnlock(c)  ->  get_varset_cell c
    | CellAt(m,a)    ->  (get_varset_mem  m) @@ (get_varset_addr a)
and get_varset_mark m =
  match m with
      VarMark v   -> V.VarSet.singleton v @@ get_varset_from_param v
    | MarkTrue    -> V.VarSet.empty
    | MarkFalse   -> V.VarSet.empty
    | Marked    c -> (get_varset_cell c)
and get_varset_bucket b =
  match b with
      VarBucket v   -> V.VarSet.singleton v @@ get_varset_from_param v
    | MkBucket (a,e,s,t) -> (get_varset_addr a) @@ (get_varset_addr e) @@
                            (get_varset_set s) @@ (get_varset_tid t)
    | BucketArrRd(bb,i)  -> (get_varset_bucketarr bb) @@
                            (get_varset_int i)
and get_varset_setth sth =
  match sth with
      VarSetTh v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySetTh         -> V.VarSet.empty
    | SinglTh(th)        -> (get_varset_tid th)
    | UnionTh(st1,st2)   -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | IntrTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | SetdiffTh(st1,st2) -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | LockSet(m,p)       -> (get_varset_mem m) @@ (get_varset_path p)
and get_varset_setelem se =
  match se with
      VarSetElem v         -> V.VarSet.singleton v @@ get_varset_from_param v
    | EmptySetElem         -> V.VarSet.empty
    | SinglElem(e)         -> (get_varset_elem e)
    | UnionElem(st1,st2)   -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | IntrElem(st1,st2)    -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | SetToElems(s,m)      -> (get_varset_set s) @@ (get_varset_mem m)
    | SetdiffElem(st1,st2) -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
and get_varset_path p =
  match p with
      VarPath v          -> V.VarSet.singleton v @@ get_varset_from_param v
    | Epsilon            -> V.VarSet.empty
    | SimplePath(a)      -> (get_varset_addr a)
    | GetPath(m,a1,a2)   -> (get_varset_mem m) @@ (get_varset_addr a1) @@ (get_varset_addr a2)
and get_varset_mem m =
  match m with
      VarMem v           -> V.VarSet.singleton v @@ get_varset_from_param v
    | Update(m,a,c)      -> (get_varset_mem m) @@ (get_varset_addr a) @@ (get_varset_cell c)



and get_varset_atom (instances:bool) (a:atom) : V.VarSet.t =
  match a with
      Append(p1,p2,p3)       -> (get_varset_path p1) @@ (get_varset_path p2) @@
                                (get_varset_path p3)
    | Reach(m,a1,a2,p)       -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                (get_varset_addr a2) @@ (get_varset_path p)
    | OrderList(m,a1,a2)     -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                (get_varset_addr a2)
    | Hashmap (m,s,se,bb,i)  -> (get_varset_mem m) @@ (get_varset_set s) @@
                                (get_varset_setelem se) @@ (get_varset_bucketarr bb) @@
                                (get_varset_int i)
    | In(a,s)                -> (get_varset_addr a) @@ (get_varset_set s)
    | SubsetEq(s1,s2)        -> (get_varset_set s1) @@ (get_varset_set s2)
    | InTh(th,st)            -> (get_varset_tid th) @@ (get_varset_setth st)
    | SubsetEqTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | InElem(e,se)           -> (get_varset_elem e) @@ (get_varset_setelem se)
    | SubsetEqElem(se1,se2)  -> (get_varset_setelem se1) @@
                                (get_varset_setelem se2)
    | Less(i1,i2)            -> (get_varset_int i1) @@ (get_varset_int i2)
    | LessEq(i1,i2)          -> (get_varset_int i1) @@ (get_varset_int i2)
    | Greater(i1,i2)         -> (get_varset_int i1) @@ (get_varset_int i2)
    | GreaterEq(i1,i2)       -> (get_varset_int i1) @@ (get_varset_int i2)
    | LessElem(e1,e2)        -> (get_varset_elem e1) @@ (get_varset_elem e2)
    | GreaterElem(e1,e2)     -> (get_varset_elem e1) @@ (get_varset_elem e2)
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
    VarT     v            -> V.VarSet.singleton v @@ get_varset_from_param v
  | SetT     s            -> get_varset_set s
  | ElemT    e            -> get_varset_elem e
  | TidT     th           -> get_varset_tid th
  | AddrT    a            -> get_varset_addr a
  | CellT    c            -> get_varset_cell c
  | SetThT   st           -> get_varset_setth st
  | SetElemT se           -> get_varset_setelem se
  | PathT    p            -> get_varset_path p
  | MemT     m            -> get_varset_mem m
  | IntT     i            -> get_varset_int i
  | TidArrayT tt          -> get_varset_tidarr tt
  | BucketArrayT bb       -> get_varset_bucketarr bb
  | MarkT    m            -> get_varset_mark m
  | BucketT  b            -> get_varset_bucket b
  | LockT  l              -> get_varset_lock l
  | LockArrayT  ll        -> get_varset_lockarr ll
  | VarUpdate(v,_,t)      -> if instances then
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


let get_termset_atom (a:atom) : TermSet.t =
  let add_list = List.fold_left (fun s e -> TermSet.add e s) TermSet.empty in
  match a with
  | Append(p1,p2,p3)       -> add_list [PathT p1; PathT p2; PathT p3]
  | Reach(m,a1,a2,p)       -> add_list [MemT m; AddrT a1; AddrT a2; PathT p]
  | OrderList(m,a1,a2)     -> add_list [MemT m; AddrT a1; AddrT a2]
  | Hashmap(m,s,se,bb,i)   -> add_list [MemT m; SetT s; SetElemT se; BucketArrayT bb; IntT i]
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
  | PC(_,th,_)             -> (match th with
                               | V.Shared  -> TermSet.empty
                               | V.Local t -> add_list [TidT (VarTh t)])
  | PCUpdate (_,th)        -> add_list [TidT th]
  | PCRange(_,_,th,_)      -> (match th with
                               | V.Shared  -> TermSet.empty
                               | V.Local t -> add_list [TidT (VarTh t)])

let termset_fs = Formula.make_fold
                    Formula.GenericLiteralFold
                    (fun _ a -> get_termset_atom a)
                    (fun _ -> TermSet.empty)
                    TermSet.union


let get_termset_from_conjformula (cf:conjunctive_formula) : TermSet.t =
  Formula.conjunctive_formula_fold termset_fs () cf


let get_termset_from_formula (phi:formula) : TermSet.t =
  Formula.formula_fold termset_fs () phi


let termset_of_sort (all:TermSet.t) (s:sort) : TermSet.t =
  let match_sort (t:term) : bool =
    match s with
    | Set         -> (match t with | SetT _           -> true | _ -> false)
    | Elem        -> (match t with | ElemT _          -> true | _ -> false)
    | Tid         -> (match t with | TidT _           -> true | _ -> false)
    | Addr        -> (match t with | AddrT _          -> true | _ -> false)
    | Cell        -> (match t with | CellT _          -> true | _ -> false)
    | SetTh       -> (match t with | SetThT _         -> true | _ -> false)
    | SetElem     -> (match t with | SetElemT _       -> true | _ -> false)
    | Path        -> (match t with | PathT _          -> true | _ -> false)
    | Mem         -> (match t with | MemT _           -> true | _ -> false)
    | Int         -> (match t with | IntT _           -> true | _ -> false)
    | TidArray    -> (match t with | TidArrayT _      -> true | _ -> false)
    | BucketArray -> (match t with | BucketArrayT _   -> true | _ -> false)
    | Mark        -> (match t with | MarkT _          -> true | _ -> false)
    | Bucket      -> (match t with | BucketT _        -> true | _ -> false)
    | Lock        -> (match t with | LockT _          -> true | _ -> false)
    | LockArray   -> (match t with | LockArrayT _     -> true | _ -> false)
    | Bool        -> (match t with
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

(*******************)
(* FLAT NORMALIZED *)
(*******************)

let is_term_var t =
  match t with
      VarT(_)             -> true
    | SetT(VarSet(_))     -> true
    | ElemT(VarElem(_))   -> true
    | TidT(VarTh  (_))   -> true
    | AddrT(VarAddr(_))   -> true
    | CellT(VarCell(_))   -> true
    | SetThT(VarSetTh(_)) -> true
    | PathT(VarPath(_))   -> true
    | MemT(VarMem(_))     -> true
    | _                   -> false
and is_set_var s =
  match s with
      VarSet _ -> true | _ -> false
and is_elem_var s =
  match s with
      VarElem _ -> true | _ -> false
and is_tid_var s =
  match s with
      VarTh _ -> true | _ -> false
and is_addr_var s =
  match s with
      VarAddr _ -> true | _ -> false
and is_cell_var s =
  match s with
      VarCell _ -> true | _ -> false
and is_mark_var s =
  match s with
      VarMark _ -> true | _ -> false
and is_setth_var s =
  match s with
      VarSetTh _ -> true | _ -> false
and is_setelem_var s =
  match s with
      VarSetElem _ -> true | _ -> false
and is_path_var s =
  match s with
      VarPath _ -> true | _ -> false
and is_mem_var s =
  match s with
      VarMem _ -> true | _ -> false
and is_int_var i =
  match i with
      VarInt _ -> true | _ -> false

let get_sort_from_term t =
  match t with
      VarT _           -> Unknown
    | SetT _           -> Set
    | ElemT _          -> Elem
    | TidT _           -> Tid
    | AddrT _          -> Addr
    | CellT _          -> Cell
    | SetThT _         -> SetTh
    | SetElemT _       -> SetElem
    | PathT _          -> Path
    | MemT _           -> Mem
    | IntT _           -> Int
    | TidArrayT _      -> TidArray
    | BucketArrayT _   -> BucketArray
    | MarkT _          -> Mark
    | BucketT _        -> Bucket
    | LockT _          -> Lock
    | LockArrayT _     -> LockArray
    | VarUpdate(v,_,_) -> (V.sort v)
  
let terms_same_type a b =
  (get_sort_from_term a) = (get_sort_from_term b)


(* TODO: propagate equalities of vars x = y *)
let rec is_term_flat t =
  match t with
      VarT(_)         -> true
    | SetT s          -> is_set_flat s
    | ElemT e         -> is_elem_flat   e
    | TidT k          -> is_tid_flat k
    | AddrT a         -> is_addr_flat a
    | CellT c         -> is_cell_flat c
    | SetThT st       -> is_setth_flat st
    | SetElemT se     -> is_setelem_flat se
    | PathT p         -> is_path_flat p
    | MemT  m         -> is_mem_flat m
    | IntT i          -> is_int_flat i
    | TidArrayT tt    -> is_tidarr_flat tt
    | BucketArrayT bb -> is_bucketarr_flat bb
    | MarkT m         -> is_mark_flat m
    | BucketT b       -> is_bucket_flat b
    | LockT l         -> is_lock_flat l
    | LockArrayT ll   -> is_lockarr_flat ll
    | VarUpdate _     -> true

and is_set_flat t =
  match t with
      VarSet _ -> true
    | EmptySet -> true
    | Singl(a) -> is_addr_flat  a
    | Union(s1,s2) -> (is_set_flat s1) && (is_set_flat s2)
    | Intr(s1,s2)  -> (is_set_flat s1) && (is_set_flat s2)
    | Setdiff(s1,s2) -> (is_set_flat s1) && (is_set_flat s2)
    | PathToSet(p)   -> (is_path_flat p)
    | AddrToSet(m,a) -> (is_mem_flat m) && (is_addr_flat a)
    | BucketRegion b -> (is_bucket_flat b)
and is_tid_flat t =
  match t with
      VarTh _         -> true
    | NoTid           -> true     
    | CellLockId(c)   -> is_cell_flat c
    | BucketTid b     -> is_bucket_flat b
    | TidArrRd (tt,i) -> (is_tidarr_flat tt) && (is_int_flat i)
    | LockId l        -> (is_lock_flat l)
and is_lock_flat x =
  match x with
      VarLock _        -> true
    | MkLock (t)       -> (is_tid_flat t)
    | LLock (l,t)      -> (is_lock_flat l) && (is_tid_flat t)
    | LUnlock (l)      -> (is_lock_flat l)
    | LockArrRd (ll,i) -> (is_lockarr_flat ll) &&
                          (is_int_flat i)
and is_lockarr_flat ll =
  match ll with
      VarLockArray _       -> true
    | LockArrayUp (ll,i,l) -> (is_lockarr_flat ll) &&
                              (is_int_flat i) &&
                              (is_lock_flat l)
and is_elem_flat t =
  match t with
      VarElem _     -> true
    | CellData(c)   -> is_cell_flat c
    | HavocListElem -> true
    | LowestElem    -> true
    | HighestElem   -> true
and is_addr_flat t =
  match t with
      VarAddr _        -> true
    | Null             -> true
    | Next(c)          -> is_cell_flat c
    | FirstLocked(m,p) -> (is_mem_flat m) && (is_path_flat p)
    | LastLocked(m,p)  -> (is_mem_flat m) && (is_path_flat p)
    | BucketInit b     -> (is_bucket_flat b)
    | BucketEnd b      -> (is_bucket_flat b)
(*    | Malloc(m,a,k)    -> (is_mem_flat m) && (is_addr_flat a) && (is_thread_flat k) *)
and is_cell_flat t =
  match t with
      VarCell _  -> true
    | Error      -> true
    | MkCell(e,a,k) -> (is_elem_flat e) && (is_addr_flat a) && (is_tid_flat k)
    | MkCellMark(e,a,k,m) -> (is_elem_flat e) && (is_addr_flat a) &&
                             (is_tid_flat k) && (is_mark_flat m)
    | CellLock(c,th)   -> (is_cell_flat c) && (is_tid_flat th)
    | CellUnlock(c) -> is_cell_flat c
    | CellAt(m,a)   -> (is_mem_flat m) && (is_addr_flat a)
and is_mark_flat m =
  match m with
      VarMark _  -> true
    | MarkTrue   -> true
    | MarkFalse  -> true
    | Marked c   -> (is_cell_flat c)
and is_bucket_flat b =
  match b with
      VarBucket _  -> true
    | MkBucket (a,e,s,t) -> (is_addr_flat a) && (is_addr_flat e) &&
                            (is_set_flat s) && (is_tid_flat t)
    | BucketArrRd(bb,i)  -> (is_bucketarr_flat bb) && (is_int_flat i)                           
and is_setth_flat t =
  match t with
      VarSetTh _ -> true
    | EmptySetTh -> true
    | SinglTh(k)         -> (is_tid_flat k)
    | UnionTh(st1,st2)   -> (is_setth_flat st1) && (is_setth_flat st2)
    | IntrTh(st1,st2)    -> (is_setth_flat st1) && (is_setth_flat st2)
    | SetdiffTh(st1,st2) -> (is_setth_flat st1) && (is_setth_flat st2)
    | LockSet(m,p)       -> (is_mem_flat m) && (is_path_flat p)
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
      VarPath _ -> true
    | Epsilon   -> true
    | SimplePath(a)    -> is_addr_flat a
    | GetPath(m,a1,a2) -> (is_mem_flat m) && (is_addr_flat a1) && (is_addr_flat a2)
and is_mem_flat t =
  match t with
      VarMem _ -> true
    | Update(m,a,c) -> (is_mem_flat m) && (is_addr_flat a) && (is_cell_flat c)
and is_int_flat i =
  match i with
      IntVal _ -> true
    | VarInt _ -> true
    | IntNeg j -> is_int_flat j
    | IntAdd (j1,j2) -> (is_int_flat j1) && (is_int_flat j2)
    | IntSub (j1,j2) -> (is_int_flat j1) && (is_int_flat j2)
    | IntMul (j1,j2) -> (is_int_flat j1) && (is_int_flat j2)
    | IntDiv (j1,j2) -> (is_int_flat j1) && (is_int_flat j2)
    | IntMod (j1,j2) -> (is_int_flat j1) && (is_int_flat j2)
    | HashCode (e)   -> (is_elem_flat e)
and is_tidarr_flat tt =
  match tt with
      VarTidArray _ -> true
    | TidArrayUp (tt,i,t) -> (is_tidarr_flat tt) &&
                             (is_int_flat i) && (is_tid_flat t)
and is_bucketarr_flat bb =
  match bb with
      VarBucketArray _ -> true
    | BucketArrayUp (bb,i,b) -> (is_bucketarr_flat bb) &&
                                (is_int_flat i) && (is_bucket_flat b)
and is_atom_flat a =
  match a with
    | Append(p1,p2,p3)       -> (is_path_flat p1) && (is_path_flat p2) &&
                                (is_path_flat p3)
    | Reach(m,a1,a2,p)       -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2) && (is_path_flat p)
    | OrderList(m,a1,a2)     -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2)
    | Hashmap(m,s,se,bb,i)   -> (is_mem_flat m) && (is_set_flat s) &&
                                (is_setelem_flat se) && (is_bucketarr_flat bb) &&
                                (is_int_flat i)
    | In(a,s)                -> (is_addr_flat a) && (is_set_flat s)
    | SubsetEq(s1,s2)        -> (is_set_flat s1) && (is_set_flat s2)
    | InTh(k,st)             -> (is_tid_flat k) && (is_setth_flat st)
    | SubsetEqTh(st1,st2)    -> (is_setth_flat st1) && (is_setth_flat st2)
    | InElem(e,se)           -> (is_elem_flat e) && (is_setelem_flat se)
    | SubsetEqElem(se1,se2)  -> (is_setelem_flat se1) && (is_setelem_flat se2)
    | Less(i1,i2)            -> (is_int_flat i1) && (is_int_flat i2)
    | LessEq(i1,i2)          -> (is_int_flat i1) && (is_int_flat i2)
    | Greater(i1,i2)         -> (is_int_flat i1) && (is_int_flat i2)
    | GreaterEq(i1,i2)       -> (is_int_flat i1) && (is_int_flat i2)
    | LessElem(e1,e2)        -> (is_elem_flat e1) && (is_elem_flat e2)
    | GreaterElem(e1,e2)     -> (is_elem_flat e1) && (is_elem_flat e2)
    | Eq(t1,t2)              -> ((is_term_flat t1) && (is_term_flat t2)  ||
                                 (is_term_flat t1) && (is_term_flat t2)  ||
                                 (is_term_flat t1) && (is_term_flat t2))
    | InEq(x,y)              -> (is_term_flat x) && (is_term_flat y)
    | BoolVar _              -> true
    | PC _                   -> true
    | PCUpdate _             -> true
    | PCRange _              -> true


let is_flat_fs = Formula.make_fold
                   Formula.GenericLiteralFold
                   (fun _ a -> is_atom_flat a)
                   (fun _ -> false)
                   (&&)

let is_literal_flat (l:literal) : bool =
  Formula.literal_fold is_flat_fs () l



(*******************)
(* PRETTY PRINTERS *)
(* WIHOUT FOLD     *)
(*******************)

let rec atom_to_str a =
  match a with
  | Append(p1,p2,pres)         -> Printf.sprintf "append(%s,%s,%s)"
                                    (path_to_str p1) (path_to_str p2)
                                    (path_to_str pres)
  | Reach(h,add_from,add_to,p) -> Printf.sprintf "reach(%s,%s,%s,%s)"
                                    (mem_to_str h) (addr_to_str add_from)
                                    (addr_to_str add_to) (path_to_str p)
  | OrderList(h,a_from,a_to)   -> Printf.sprintf "orderlist(%s,%s,%s)"
                                    (mem_to_str h) (addr_to_str a_from)
                                    (addr_to_str a_to)
  | Hashmap(h,s,se,bb,i)       -> Printf.sprintf "hashmap(%s,%s,%s,%s,%s)"
                                                  (mem_to_str h)
                                                  (set_to_str s)
                                                  (setelem_to_str se)
                                                  (bucketarr_to_str bb)
                                                  (integer_to_str i)
  | In(a,s)                    -> Printf.sprintf "%s in %s "
                                    (addr_to_str a) (set_to_str s)
  | SubsetEq(s_in,s_out)       -> Printf.sprintf "%s subseteq %s"
                                    (set_to_str s_in) (set_to_str s_out)
  | InTh(th,s)                 -> Printf.sprintf "%s inTh %s"
                                    (tid_to_str th) (setth_to_str s)
  | SubsetEqTh(s_in,s_out)     -> Printf.sprintf "%s subseteqTh %s"
                                    (setth_to_str s_in) (setth_to_str s_out)
  | InElem(e,s)                -> Printf.sprintf "%s inElem %s"
                                    (elem_to_str e) (setelem_to_str s)
  | SubsetEqElem(s_in,s_out)   -> Printf.sprintf "%s subseteqElem %s"
                                    (setelem_to_str s_in) (setelem_to_str s_out)
  | Less (i1,i2)               -> Printf.sprintf "%s < %s"
                                    (integer_to_str i1) (integer_to_str i2)
  | LessEq (i1,i2)             -> Printf.sprintf "%s <= %s"
                                    (integer_to_str i1) (integer_to_str i2)
  | Greater (i1,i2)            -> Printf.sprintf "%s > %s"
                                    (integer_to_str i1) (integer_to_str i2)
  | GreaterEq (i1,i2)          -> Printf.sprintf "%s >= %s"
                                    (integer_to_str i1) (integer_to_str i2)
  | LessElem(e1,e2)            -> Printf.sprintf "%s < %s"
                                    (elem_to_str e1) (elem_to_str e2)
  | GreaterElem(e1,e2)         -> Printf.sprintf "%s < %s"
                                    (elem_to_str e1) (elem_to_str e2)
  | Eq(exp)                    -> eq_to_str (exp)
  | InEq(exp)                  -> diseq_to_str (exp)
  | BoolVar v                  -> V.to_str v
  | PC (pc,t,pr)               -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = V.shared_or_local_to_str t in
                                  Printf.sprintf "%s(%s) = %i" pc_str th_str pc
  | PCUpdate (pc,t)            -> let th_str = tid_to_str t in
                                  Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,t,pr)     -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = V.shared_or_local_to_str t in
                                  Printf.sprintf "%i <= %s(%s) <= %i"
                                                  pc1 pc_str th_str pc2

and mem_to_str expr =
  match expr with
      VarMem(v) -> V.to_str v
    | Update(mem,add,cell) -> Printf.sprintf "upd(%s,%s,%s)"
  (mem_to_str mem) (addr_to_str add) (cell_to_str cell)
and integer_to_str expr =
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
  | IntMod (i1,i2)    -> sprintf "%s %% %s" (integer_to_str i1)
                                            (integer_to_str i2)
  | HashCode (e)      -> sprintf "hashCode(%s)" (elem_to_str e)
and tidarr_to_str expr : string =
  match expr with
    VarTidArray v       -> V.to_str v
  | TidArrayUp(arr,i,b) -> Printf.sprintf "tidArrUpd(%s,%s,%s)"
                                        (tidarr_to_str arr)
                                        (integer_to_str i)
                                        (tid_to_str b)
and bucketarr_to_str expr : string =
  match expr with
    VarBucketArray v       -> V.to_str v
  | BucketArrayUp(arr,i,b) -> Printf.sprintf "bucketArrUpd(%s,%s,%s)"
                                        (bucketarr_to_str arr)
                                        (integer_to_str i)
                                        (bucket_to_str b)
and path_to_str expr =
  match expr with
      VarPath(v) -> V.to_str v
    | Epsilon -> Printf.sprintf "epsilon"
    | SimplePath(addr) -> Printf.sprintf "[ %s ]" (addr_to_str addr)
    | GetPath(mem,add_from,add_to) -> Printf.sprintf "getp(%s,%s,%s)"
  (mem_to_str mem) (addr_to_str add_from) (addr_to_str add_to)
and set_to_str e =
  match e with
      VarSet(v)  -> V.to_str v
    | EmptySet  -> "empty"
    | Singl(addr) -> Printf.sprintf "{ %s }" (addr_to_str addr)
    | Union(s1,s2) -> Printf.sprintf "union(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | Intr(s1,s2) -> Printf.sprintf "intr(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | Setdiff(s1,s2) -> Printf.sprintf "diff(%s,%s)"
                              (set_to_str s1) (set_to_str s2)
    | PathToSet(path) -> Printf.sprintf "path2set(%s)"
                              (path_to_str path)
    | AddrToSet(mem,addr) -> Printf.sprintf "addr2set(%s,%s)"
                              (mem_to_str mem) (addr_to_str addr)
    | BucketRegion(b)     -> sprintf "%s.breg" (bucket_to_str b)
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
    | LockSet(m,p) -> Printf.sprintf "lockset(%s,%s)"
                            (mem_to_str m) (path_to_str p)
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
    | SetdiffElem(s_1,s_2) -> Printf.sprintf "ediff(%s,%s)"
                            (setelem_to_str s_1) (setelem_to_str s_2)
and cell_to_str e =
  match e with
      VarCell(v) -> V.to_str v
    | Error -> "Error"
    | MkCell(data,addr,th) -> Printf.sprintf "mkcell(%s,%s,%s)"
                                (elem_to_str data) (addr_to_str addr) (tid_to_str th)
    | MkCellMark(data,addr,th,m) -> Printf.sprintf "mkcell(%s,%s,%s,%s)"
                                      (elem_to_str data) (addr_to_str addr)
                                      (tid_to_str th) (mark_to_str m)
    | CellLock(cell,th)   -> Printf.sprintf "%s.lock(%s)"
                              (cell_to_str cell) (tid_to_str th)
    | CellUnlock(cell) -> Printf.sprintf "%s.unlock"
                            (cell_to_str cell)
    | CellAt(mem,addr) -> Printf.sprintf "%s [ %s ]" (mem_to_str mem) (addr_to_str addr)   
and mark_to_str expr =
  match expr with
      VarMark(v) -> V.to_str v
    | MarkTrue  -> "T"
    | MarkFalse -> "F"
    | Marked c  -> Printf.sprintf "%s.marked" (cell_to_str c)
and bucket_to_str expr :string =
  match expr with
    VarBucket v -> V.to_str v
  | MkBucket (i,e,s,t) -> Printf.sprintf "mkbucket(%s,%s,%s,%s)" (addr_to_str i)
                                                                 (addr_to_str e)
                                                                 (set_to_str s)
                                                                 (tid_to_str t)
  | BucketArrRd(bb,i)  -> Printf.sprintf "%s[%s]" (bucketarr_to_str bb)
                                                  (integer_to_str i)   
and addr_to_str expr =
  match expr with
      VarAddr(v) -> V.to_str v
    | Null                  -> "null"
    | Next(cell)            -> Printf.sprintf "%s.next" (cell_to_str cell)
    | FirstLocked(mem,path) -> Printf.sprintf "firstlocked(%s,%s)"
                                (mem_to_str mem) (path_to_str path)
    | LastLocked(mem,path)  -> Printf.sprintf "lastlocked(%s,%s)"
                                (mem_to_str mem) (path_to_str path)
(*    | Malloc(e,a,t)     -> Printf.sprintf "malloc(%s,%s,%s)" (elem_to_str e) (addr_to_str a) (tid_to_str t) *)
    | BucketInit(b)         -> Printf.sprintf "%s.binit" (bucket_to_str b)
    | BucketEnd(b)          -> Printf.sprintf "%s.bend" (bucket_to_str b)
and tid_to_str th =
  match th with
      VarTh(v)         -> V.to_str v
    | NoTid            -> Printf.sprintf "NoTid"
    | CellLockId(cell) -> Printf.sprintf "%s.lockid" (cell_to_str cell)
    | BucketTid b      -> Printf.sprintf "%s.btid" (bucket_to_str b)
    | TidArrRd(arr,l)  -> Printf.sprintf "%s[%s]" (tidarr_to_str arr)
                                                  (integer_to_str l)
    | LockId (l)       -> Printf.sprintf "%s.id" (lock_to_str l)
and lock_to_str (expr:lock) : string =
  match expr with
    VarLock v        -> V.to_str v
  | MkLock (t)       -> sprintf "mklock(%s)" (tid_to_str t)
  | LLock (l,t)      -> sprintf "lock(%s,%s)" (lock_to_str l) (tid_to_str t)
  | LUnlock (l)      -> sprintf "unlock(%s)" (lock_to_str l)
  | LockArrRd (ll,i) -> sprintf "%s[%s]" (lockarr_to_str ll) (integer_to_str i)
and lockarr_to_str (expr:lockarr) : string =
  match expr with
    VarLockArray v       -> V.to_str v
  | LockArrayUp(arr,i,l) -> sprintf "%s{%s<-%s}" (lockarr_to_str arr)
                                                 (integer_to_str i)
                                                 (lock_to_str l)
and eq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s = %s" (term_to_str e1) (term_to_str e2)
and diseq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s != %s" (term_to_str e1) (term_to_str e2)
and elem_to_str elem =
  match elem with
      VarElem(v)     -> V.to_str v
    | CellData(cell) -> Printf.sprintf "%s.data" (cell_to_str cell)
    | HavocListElem  -> "havocListElem()"
    | LowestElem     -> "lowestElem"
    | HighestElem    -> "highestElem"
and term_to_str expr =
  match expr with
      VarT(v) -> V.to_str v
    | SetT(set)          -> (set_to_str set)
    | AddrT(addr)        -> (addr_to_str addr)
    | ElemT(elem)        -> (elem_to_str elem)
    | TidT(th)           -> (tid_to_str th)
    | CellT(cell)        -> (cell_to_str cell)
    | SetThT(setth)      -> (setth_to_str setth)
    | SetElemT(setelem)  -> (setelem_to_str setelem)
    | PathT(path)        -> (path_to_str path)
    | MemT(mem)          -> (mem_to_str mem)
    | IntT(i)            -> (integer_to_str i)
    | TidArrayT(tt)      -> (tidarr_to_str tt)
    | BucketArrayT(bb)   -> (bucketarr_to_str bb)
    | MarkT(m)           -> (mark_to_str m)
    | BucketT(b)         -> (bucket_to_str b)
    | LockT(l)           -> (lock_to_str l)
    | LockArrayT(ll)     -> (lockarr_to_str ll)
    | VarUpdate (v,th,t) -> let v_str = V.to_str v in
                            let th_str = tid_to_str th in
                            let t_str = term_to_str t in
                              Printf.sprintf "%s{%s<-%s}" v_str th_str t_str


and literal_to_str (l:literal) : string =
  Formula.literal_to_str atom_to_str l

let conjunctive_formula_to_str (cf:conjunctive_formula) : string =
  Formula.conjunctive_formula_to_str atom_to_str cf

and formula_to_str (phi:formula) : string =
  Formula.formula_to_str atom_to_str phi

let sort_to_str s =
  match s with
      Set         -> "Set"
    | Elem        -> "Elem"
    | Tid         -> "Tid"
    | Addr        -> "Addr"
    | Cell        -> "Cell"
    | SetTh       -> "SetTh"
    | SetElem     -> "SetElem"
    | Path        -> "Path"
    | Mem         -> "Mem"
    | Int         -> "Int"
    | TidArray    -> "TidArr"
    | BucketArray -> "BucketArr"
    | Bool        -> "Bool"
    | Mark        -> "Mark"
    | Bucket      -> "Bucket"
    | Lock        -> "TLock"
    | LockArray   -> "LockArray"
    | Unknown     -> "Unknown"

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
let (@@) = ThreadSet.union

let rec get_tid_in (v:V.t) : ThreadSet.t =
  match V.parameter v with
  | V.Shared -> ThreadSet.empty
  | V.Local t -> ThreadSet.singleton (VarTh t)


and voc_term (expr:term) : ThreadSet.t =
  match expr with
    | VarT v             -> (match (V.sort v) with
                             | Tid -> ThreadSet.singleton (VarTh v)
                             | _    -> ThreadSet.empty ) @@ get_tid_in v
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
    | TidArrayT(tt)      -> voc_tidarr tt
    | BucketArrayT(bb)   -> voc_bucketarr bb
    | MarkT(m)           -> voc_mark m
    | BucketT(b)         -> voc_bucket b
    | LockT(l)           -> voc_lock l
    | LockArrayT(ll)     -> voc_lockarr ll
    | VarUpdate (v,th,t) -> (get_tid_in v) @@ (voc_tid th) @@ (voc_term t)



and voc_set (e:set) : ThreadSet.t =
  match e with
    VarSet v            -> get_tid_in v
  | EmptySet            -> ThreadSet.empty
  | Singl(addr)         -> (voc_addr addr)
  | Union(s1,s2)        -> (voc_set s1) @@ (voc_set s2)
  | Intr(s1,s2)         -> (voc_set s1) @@ (voc_set s2)
  | Setdiff(s1,s2)      -> (voc_set s1) @@ (voc_set s2)
  | PathToSet(path)     -> (voc_path path)
  | AddrToSet(mem,addr) -> (voc_mem mem) @@ (voc_addr addr)
  | BucketRegion b      -> (voc_bucket b)


and voc_addr (a:addr) : ThreadSet.t =
  match a with
    VarAddr v             -> get_tid_in v
  | Null                  -> ThreadSet.empty
  | Next(cell)            -> (voc_cell cell)
  | FirstLocked(mem,path) -> (voc_mem mem) @@ (voc_path path)
  | LastLocked(mem,path)  -> (voc_mem mem) @@ (voc_path path)
  | BucketInit b          -> (voc_bucket b)
  | BucketEnd b           -> (voc_bucket b)


and voc_elem (e:elem) : ThreadSet.t =
  match e with
    VarElem v          -> get_tid_in v
  | CellData(cell)     -> (voc_cell cell)
  | HavocListElem      -> ThreadSet.empty
  | LowestElem         -> ThreadSet.empty
  | HighestElem        -> ThreadSet.empty


and voc_tid (th:tid) : ThreadSet.t =
  match th with
    VarTh v            -> ThreadSet.add th (get_tid_in v)
  | NoTid              -> ThreadSet.empty
  | CellLockId(cell)   -> (voc_cell cell)
  | BucketTid b        -> (voc_bucket b)
  | TidArrRd (tt,i)    -> (voc_tidarr tt) @@ (voc_int i)
  | LockId l           -> (voc_lock l)

and voc_lock (x:lock) : ThreadSet.t =
  match x with
    VarLock v        -> get_tid_in v
  | MkLock (t)       -> (voc_tid t)
  | LLock (l,t)      -> (voc_lock l) @@ (voc_tid t)
  | LUnlock (l)      -> (voc_lock l)
  | LockArrRd (ll,i) -> (voc_lockarr ll) @@ (voc_int i)

and voc_lockarr (ll:lockarr) : ThreadSet.t =
  match ll with
    VarLockArray v       -> get_tid_in v
  | LockArrayUp (ll,i,l) -> (voc_lockarr ll) @@ (voc_int i) @@ (voc_lock l)

and voc_cell (c:cell) : ThreadSet.t =
  match c with
    VarCell v                  -> get_tid_in v
  | Error                      -> ThreadSet.empty
  | MkCell(data,addr,th)       -> (voc_elem data) @@
                                  (voc_addr addr) @@
                                  (voc_tid th)
  | MkCellMark(data,addr,th,m) -> (voc_elem data) @@
                                  (voc_addr addr) @@
                                  (voc_tid th)    @@
                                  (voc_mark m)
  | CellLock(cell,th)          -> (voc_cell cell) @@ (voc_tid th)
  | CellUnlock(cell)           -> (voc_cell cell)
  | CellAt(mem,addr)           -> (voc_mem mem) @@ (voc_addr addr)


and voc_mark (m:mark) : ThreadSet.t =
  match m with
    VarMark v -> get_tid_in v
  | MarkTrue  -> ThreadSet.empty
  | MarkFalse -> ThreadSet.empty
  | Marked c  -> (voc_cell c)


and voc_bucket (b:bucket) : ThreadSet.t =
  match b with
    VarBucket v -> get_tid_in v
  | MkBucket (a,e,s,t) -> (voc_addr a) @@ (voc_addr e) @@
                          (voc_set s) @@ (voc_tid t)
  | BucketArrRd(bb,i)  -> (voc_bucketarr bb) @@ (voc_int i)


and voc_setth (s:setth) : ThreadSet.t =
  match s with
    VarSetTh v          -> get_tid_in v
  | EmptySetTh          -> ThreadSet.empty
  | SinglTh(th)         -> (voc_tid th)
  | UnionTh(s1,s2)      -> (voc_setth s1) @@ (voc_setth s2)
  | IntrTh(s1,s2)       -> (voc_setth s1) @@ (voc_setth s2)
  | SetdiffTh(s1,s2)    -> (voc_setth s1) @@ (voc_setth s2)
  | LockSet(m,p)        -> (voc_mem m) @@ (voc_path p)


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
    VarPath v                -> get_tid_in v
  | Epsilon                  -> ThreadSet.empty
  | SimplePath(addr)         -> (voc_addr addr)
  | GetPath(mem,a_from,a_to) -> (voc_mem mem) @@
                                (voc_addr a_from) @@
                                (voc_addr a_to)


and voc_mem (m:mem) : ThreadSet.t =
  match m with
    VarMem v             -> get_tid_in v
  | Update(mem,add,cell) -> (voc_mem mem) @@ (voc_addr add) @@ (voc_cell cell)


and voc_int (i:integer) : ThreadSet.t =
  match i with
    IntVal _          -> ThreadSet.empty
  | VarInt v          -> get_tid_in v
  | IntNeg(i)         -> (voc_int i)
  | IntAdd(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntSub(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntMul(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntDiv(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | IntMod(i1,i2)     -> (voc_int i1) @@ (voc_int i2)
  | HashCode(e)       -> (voc_elem e)


and voc_tidarr (tt:tidarr) : ThreadSet.t =
  match tt with
    VarTidArray v   -> get_tid_in v
  | TidArrayUp (tt,i,t) -> (voc_tidarr tt) @@ (voc_int i) @@
                           (voc_tid t)


and voc_bucketarr (bb:bucketarr) : ThreadSet.t =
  match bb with
    VarBucketArray v   -> get_tid_in v
  | BucketArrayUp (bb,i,b) -> (voc_bucketarr bb) @@ (voc_int i) @@
                              (voc_bucket b)


and voc_atom (a:atom) : ThreadSet.t =
  match a with
    Append(p1,p2,pres)         -> (voc_path p1) @@
                                  (voc_path p2) @@
                                  (voc_path pres)
  | Reach(h,add_from,add_to,p) -> (voc_mem h) @@
                                  (voc_addr add_from) @@
                                  (voc_addr add_to) @@
                                  (voc_path p)
  | OrderList(h,a_from,a_to)   -> (voc_mem h) @@
                                  (voc_addr a_from) @@
                                  (voc_addr a_to)
  | Hashmap(h,s,se,bb,i)       -> (voc_mem h) @@
                                  (voc_set s) @@
                                  (voc_setelem se) @@
                                  (voc_bucketarr bb) @@
                                  (voc_int i)
  | In(a,s)                    -> (voc_addr a) @@ (voc_set s)
  | SubsetEq(s_in,s_out)       -> (voc_set s_in) @@ (voc_set s_out)
  | InTh(th,s)                 -> (voc_tid th) @@ (voc_setth s)
  | SubsetEqTh(s_in,s_out)     -> (voc_setth s_in) @@ (voc_setth s_out)
  | InElem(e,s)                -> (voc_elem e) @@ (voc_setelem s)
  | SubsetEqElem(s_in,s_out)   -> (voc_setelem s_in) @@ (voc_setelem s_out)
  | Less(i1,i2)                -> (voc_int i1) @@ (voc_int i2)
  | LessEq(i1,i2)              -> (voc_int i1) @@ (voc_int i2)
  | Greater(i1,i2)             -> (voc_int i1) @@ (voc_int i2)
  | GreaterEq(i1,i2)           -> (voc_int i1) @@ (voc_int i2)
  | LessElem(e1,e2)            -> (voc_elem e1) @@ (voc_elem e2)
  | GreaterElem(e1,e2)         -> (voc_elem e1) @@ (voc_elem e2)
  | Eq(exp)                    -> (voc_eq exp)
  | InEq(exp)                  -> (voc_ineq exp)
  | BoolVar v                  -> get_tid_in v
  | PC (_,t,_)                 -> (match t with
                                   | V.Shared -> ThreadSet.empty
                                   | V.Local x -> ThreadSet.singleton (VarTh x))
  | PCUpdate (_,t)             -> ThreadSet.singleton t
  | PCRange (_,_,t,_)          -> (match t with
                                   | V.Shared -> ThreadSet.empty
                                   | V.Local x -> ThreadSet.singleton (VarTh x))


and voc_eq ((t1,t2):eq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


and voc_ineq ((t1,t2):diseq) : ThreadSet.t = (voc_term t1) @@ (voc_term t2)


let voc_fs = Formula.make_fold
               Formula.GenericLiteralFold
               (fun _ a -> voc_atom a)
               (fun _ -> ThreadSet.empty)
               (@@)

let voc_conjunctive_formula (cf:atom Formula.conjunctive_formula) : ThreadSet.t =
  Formula.conjunctive_formula_fold voc_fs () cf


let voc_formula (phi:atom Formula.formula) : ThreadSet.t =
  Formula.formula_fold voc_fs () phi


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
  let empty = SortSet.empty in
  let union = SortSet.union in
  let add = SortSet.add in
  let single = SortSet.singleton in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in

  let rec req_atom (a:atom) : SortSet.t =
    match a with
    | Append (p1,p2,p3)     -> list_union [req_p p1;req_p p1;req_p p2;req_p p3]
    | Reach (m,a1,a2,p)     -> list_union [req_m m;req_a a1;req_a a2;req_p p]
    | OrderList (m,a1,a2)   -> list_union [req_m m;req_a a1;req_a a2]
    | Hashmap (m,s,se,bb,i) -> list_union [req_m m;req_s s;req_se se;
                                           req_bb bb; req_i i]
    | In (a,s)              -> list_union [req_a a;req_s s]
    | SubsetEq (s1,s2)      -> list_union [req_s s1;req_s s2]
    | InTh (t,s)            -> list_union [req_t t;req_st s]
    | SubsetEqTh (s1,s2)    -> list_union [req_st s1;req_st s2]
    | InElem (e,s)          -> list_union [req_e e;req_se s]
    | SubsetEqElem (s1,s2)  -> list_union [req_se s1;req_se s2]
    | Less (i1,i2)          -> list_union [req_i i1; req_i i2]
    | LessEq (i1,i2)        -> list_union [req_i i1; req_i i2]
    | Greater (i1,i2)       -> list_union [req_i i1; req_i i2]
    | GreaterEq (i1,i2)     -> list_union [req_i i1; req_i i2]
    | LessElem  (e1,e2)     -> list_union [req_e e1; req_e e2]
    | GreaterElem (e1,e2)   -> list_union [req_e e1; req_e e2]
    | Eq (t1,t2)            -> union (req_term t1) (req_term t2)
    | InEq (t1,t2)          -> union (req_term t1) (req_term t2)
    | BoolVar _             -> single Bool
    | PC _                  -> empty
    | PCUpdate _            -> empty
    | PCRange _             -> empty

  and req_m (m:mem) : SortSet.t =
    match m with
    | VarMem _         -> single Mem
    | Update (m,a,c)   -> append Mem [req_m m;req_a a;req_c c]

  and req_i (i:integer) : SortSet.t =
    match i with
    | IntVal _         -> single Int
    | VarInt _         -> single Int
    | IntNeg i         -> append Int [req_i i]
    | IntAdd (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntSub (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntMul (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntDiv (i1,i2)   -> append Int [req_i i1;req_i i2]
    | IntMod (i1,i2)   -> append Int [req_i i1;req_i i2]
    | HashCode (e)     -> append Int [req_e e]

  and req_bb (bb:bucketarr) : SortSet.t =
    match bb with
    | VarBucketArray _       -> single BucketArray
    | BucketArrayUp (bb,i,b) -> append BucketArray [req_bb bb; req_i i; req_b b]

  and req_p (p:path) : SortSet.t =
    match p with
    | VarPath _         -> single Path
    | Epsilon           -> single Path
    | SimplePath a      -> append Path [req_a a]
    | GetPath (m,a1,a2) -> append Path [req_m m;req_a a1;req_a a2]

  and req_st (s:setth) : SortSet.t =
    match s with
    | VarSetTh _         -> single SetTh
    | EmptySetTh         -> single SetTh
    | SinglTh t          -> append SetTh [req_t t]
    | UnionTh (s1,s2)    -> append SetTh [req_st s1;req_st s2]
    | IntrTh (s1,s2)     -> append SetTh [req_st s1;req_st s2]
    | SetdiffTh (s1,s2)  -> append SetTh [req_st s1;req_st s2]
    | LockSet(m,p)       -> append SetTh [req_m m;req_p p]

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
    | VarCell _            -> single Cell
    | Error                -> single Cell
    | MkCell (e,a,t)       -> append Cell [req_e e;req_a a; req_t t]
    | MkCellMark (e,a,t,m) -> append Cell [req_e e;req_a a; req_t t; req_mk m]
    | CellLock (c,t)       -> append Cell [req_c c;req_t t]
    | CellUnlock c         -> append Cell [req_c c]
    | CellAt (m,a)         -> append Cell [req_m m;req_a a]

  and req_mk (m:mark) : SortSet.t =
    match m with
    | VarMark _ -> single Mark
    | MarkTrue  -> single Mark
    | MarkFalse -> single Mark
    | Marked c  -> append Mark [req_c c]

  and req_b (b:bucket) : SortSet.t =
    match b with
    | VarBucket _        -> single Bucket
    | MkBucket (i,e,s,t) -> append Bucket [req_a i; req_a e; req_s s; req_t t]
    | BucketArrRd (bb,i) -> append Bucket [req_bb bb; req_i i]

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _         -> single Addr
    | Null              -> single Addr
    | Next c            -> append Addr [req_c c]
    | FirstLocked (m,p) -> append Addr [req_m m;req_p p]
    | LastLocked (m,p)  -> append Addr [req_m m;req_p p]
    | BucketInit b      -> append Addr [req_b b]
    | BucketEnd b       -> append Addr [req_b b]

  and req_e (e:elem) : SortSet.t =
    match e with
    | VarElem _         -> single Elem
    | CellData c        -> append Elem [req_c c]
    | HavocListElem     -> single Elem
    | LowestElem        -> single Elem
    | HighestElem       -> single Elem

  and req_t (t:tid) : SortSet.t =
    match t with
    | VarTh _           -> single Tid
    | NoTid             -> single Tid
    | CellLockId c      -> append Tid [req_c c]
    | BucketTid b       -> append Tid [req_b b]
    | TidArrRd (tt,i)   -> append Tid [req_tt tt;req_i i]
    | LockId l          -> append Tid [req_l l]

  and req_l (x:lock) : SortSet.t =
    match x with
    | VarLock _        -> single Lock
    | MkLock (t)       -> append Lock [req_t t]
    | LLock (l,t)      -> append Lock [req_l l; req_t t]
    | LUnlock (l)      -> append Lock [req_l l]
    | LockArrRd (ll,i) -> append Lock [req_ll ll; req_i i]

  and req_ll (ll:lockarr) : SortSet.t =
    match ll with
    | VarLockArray _       -> single LockArray
    | LockArrayUp (ll,i,l) -> append LockArray [req_ll ll; req_i i; req_l l]

  and req_tt (tt:tidarr) : SortSet.t =
    match tt with
    | VarTidArray _       -> single TidArray
    | TidArrayUp (tt,i,t) -> append TidArray [req_tt tt; req_i i; req_t t]

  and req_s (s:set) : SortSet.t =
    match s with
    | VarSet _         -> single Set
    | EmptySet         -> single Set
    | Singl a          -> append Set [req_a a]
    | Union (s1,s2)    -> append Set [req_s s1;req_s s2]
    | Intr (s1,s2)     -> append Set [req_s s1;req_s s2]
    | Setdiff (s1,s2)  -> append Set [req_s s1;req_s s2]
    | PathToSet p      -> append Set [req_p p]
    | AddrToSet (m,a)  -> append Set [req_m m;req_a a]
    | BucketRegion b   -> append Set [req_b b]

  and req_term (t:term) : SortSet.t =
    match t with
    | VarT v             -> single (V.sort v)
    | SetT s             -> req_s s
    | ElemT e            -> req_e e
    | TidT t             -> req_t t
    | AddrT a            -> req_a a
    | CellT c            -> req_c c
    | SetThT s           -> req_st s
    | SetElemT s         -> req_se s
    | PathT p            -> req_p p
    | MemT m             -> req_m m
    | IntT i             -> req_i i
    | TidArrayT tt       -> req_tt tt
    | BucketArrayT bb    -> req_bb bb
    | MarkT m            -> req_mk m
    | BucketT b          -> req_b b
    | LockT l            -> req_l l
    | LockArrayT ll      -> req_ll ll
    | VarUpdate (v,t,tr) -> append (V.sort v) [req_t t;req_term tr] in

  let req_fs = Formula.make_fold
                 Formula.GenericLiteralFold
                 (fun _ a -> req_atom a)
                 (fun _ -> empty)
                 union in

  let req_f (phi:formula) : SortSet.t =
    Formula.formula_fold req_fs () phi

  in
    SortSet.elements (req_f phi)

 

let special_ops (phi:formula) : special_op_t list =
  let empty = OpsSet.empty in
  let union = OpsSet.union in
  let add = OpsSet.add in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in

  let rec ops_atom (a:atom) : OpsSet.t =
    match a with
    | Append (p1,p2,p3)     -> list_union [ops_p p1;ops_p p1;ops_p p2;ops_p p3]
    | Reach (m,a1,a2,p)     -> append Reachable[ops_m m;ops_a a1;ops_a a2;ops_p p]
    | OrderList (m,a1,a2)   -> append OrderedList[ops_m m;ops_a a1;ops_a a2]
    | Hashmap (m,s,se,bb,i) -> append HashMap[ops_m m; ops_s s; ops_se se;
                                              ops_bb bb; ops_i i]
    | In (a,s)              -> list_union [ops_a a;ops_s s]
    | SubsetEq (s1,s2)      -> list_union [ops_s s1;ops_s s2]
    | InTh (t,s)            -> list_union [ops_t t;ops_st s]
    | SubsetEqTh (s1,s2)    -> list_union [ops_st s1;ops_st s2]
    | InElem (e,s)          -> list_union [ops_e e;ops_se s]
    | SubsetEqElem (s1,s2)  -> list_union [ops_se s1;ops_se s2]
    | Less (i1,i2)          -> list_union [ops_i i1; ops_i i2]
    | LessEq (i1,i2)        -> list_union [ops_i i1; ops_i i2]
    | Greater (i1,i2)       -> list_union [ops_i i1; ops_i i2]
    | GreaterEq (i1,i2)     -> list_union [ops_i i1; ops_i i2]
    | LessElem (e1,e2)      -> append ElemOrder [ops_e e1; ops_e e2]
    | GreaterElem (e1,e2)   -> append ElemOrder [ops_e e1; ops_e e2]
    | Eq (t1,t2)            -> list_union [ops_term t1;ops_term t2]
    | InEq (t1,t2)          -> list_union [ops_term t1;ops_term t2]
    | BoolVar _             -> empty
    | PC _                  -> empty
    | PCUpdate _            -> empty
    | PCRange _             -> empty

  and ops_m (m:mem) : OpsSet.t =
    match m with
    | VarMem _         -> empty
    | Update (m,a,c)   -> list_union [ops_m m;ops_a a;ops_c c]

  and ops_i (i:integer) : OpsSet.t =
    match i with
    | IntVal _ -> empty
    | VarInt _ -> empty
    | IntNeg j -> list_union [ops_i j]
    | IntAdd (j1,j2) -> list_union [ops_i j1; ops_i j2]
    | IntSub (j1,j2) -> list_union [ops_i j1; ops_i j2]
    | IntMul (j1,j2) -> list_union [ops_i j1; ops_i j2]
    | IntDiv (j1,j2) -> list_union [ops_i j1; ops_i j2]
    | IntMod (j1,j2) -> list_union [ops_i j1; ops_i j2]
    | HashCode (e)   -> list_union [ops_e e]

  and ops_tt (tt:tidarr) : OpsSet.t =
    match tt with
    | VarTidArray _ -> empty
    | TidArrayUp (tt,i,t) -> list_union [ops_tt tt; ops_i i; ops_t t]

  and ops_bb (bb:bucketarr) : OpsSet.t =
    match bb with
    | VarBucketArray _ -> empty
    | BucketArrayUp (bb,i,b) -> list_union [ops_bb bb; ops_i i; ops_b b]

  and ops_p (p:path) : OpsSet.t =
    match p with
    | VarPath _         -> empty
    | Epsilon           -> empty
    | SimplePath a      -> ops_a a
    | GetPath (m,a1,a2) -> append Getp [ops_m m;ops_a a1;ops_a a2]

  and ops_st (s:setth) : OpsSet.t =
    match s with
    | VarSetTh _         -> empty
    | EmptySetTh         -> empty
    | SinglTh t          -> ops_t t
    | UnionTh (s1,s2)    -> list_union [ops_st s1;ops_st s2]
    | IntrTh (s1,s2)     -> list_union [ops_st s1;ops_st s2]
    | SetdiffTh (s1,s2)  -> list_union [ops_st s1;ops_st s2]
    | LockSet (m,p)      -> append Lockset [ops_m m;ops_p p]

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
    | VarCell _            -> empty
    | Error                -> empty
    | MkCell (e,a,t)       -> list_union [ops_e e;ops_a a; ops_t t]
    | MkCellMark (e,a,t,m) -> list_union [ops_e e;ops_a a; ops_t t; ops_mk m]
    | CellLock (c,t)       -> list_union [ops_c c;ops_t t]
    | CellUnlock c         -> list_union [ops_c c]
    | CellAt (m,a)         -> list_union [ops_m m;ops_a a]

  and ops_mk (m:mark) : OpsSet.t =
    match m with
    | VarMark _ -> empty
    | MarkTrue  -> empty
    | MarkFalse -> empty
    | Marked c  -> ops_c c

  and ops_b (b:bucket) : OpsSet.t =
    match b with
    | VarBucket _        -> empty
    | MkBucket(i,e,s,t)  -> list_union [ops_a i; ops_a e; ops_s s; ops_t t]
    | BucketArrRd (bb,i) -> list_union [ops_bb bb; ops_i i]

  and ops_a (a:addr) : OpsSet.t =
    match a with
    | VarAddr _         -> empty
    | Null              -> empty
    | Next c            -> list_union [ops_c c]
    | FirstLocked (m,p) -> append FstLocked [ops_m m;ops_p p]
    | LastLocked (m,p)  -> append LstLocked [ops_m m;ops_p p]
    | BucketInit b      -> ops_b b
    | BucketEnd b       -> ops_b b

  and ops_e (e:elem) : OpsSet.t =
    match e with
    | VarElem _         -> empty
    | CellData c        -> ops_c c
    | HavocListElem     -> empty
    | LowestElem        -> empty
    | HighestElem       -> empty

  and ops_t (t:tid) : OpsSet.t =
    match t with
    | VarTh _         -> empty
    | NoTid           -> empty
    | CellLockId c    -> ops_c c
    | BucketTid b     -> ops_b b
    | TidArrRd (tt,i) -> list_union [ops_tt tt; ops_i i]
    | LockId l        -> ops_l l

  and ops_l (x:lock) : OpsSet.t =
    match x with
    | VarLock _        -> empty
    | MkLock (t)       -> ops_t t
    | LLock (l,t)      -> list_union [ops_l l; ops_t t]
    | LUnlock (l)      -> ops_l l
    | LockArrRd (ll,i) -> list_union [ops_ll ll; ops_i i]
    
  and ops_ll (ll:lockarr) : OpsSet.t =
    match ll with
    | VarLockArray _       -> empty
    | LockArrayUp (ll,i,l) -> list_union [ops_ll ll; ops_i i; ops_l l]

  and ops_s (s:set) : OpsSet.t =
    match s with
    | VarSet _         -> empty
    | EmptySet         -> empty
    | Singl a          -> ops_a a
    | Union (s1,s2)    -> list_union [ops_s s1;ops_s s2]
    | Intr (s1,s2)     -> list_union [ops_s s1;ops_s s2]
    | Setdiff (s1,s2)  -> list_union [ops_s s1;ops_s s2]
    | PathToSet p      -> append Path2Set [ops_p p]
    | AddrToSet (m,a)  -> append Addr2Set [ops_m m;ops_a a]
    | BucketRegion b   -> ops_b b

  and ops_term (t:term) : OpsSet.t =
    match t with
    | VarT _             -> empty
    | SetT s             -> ops_s s
    | ElemT e            -> ops_e e
    | TidT t             -> ops_t t
    | AddrT a            -> ops_a a
    | CellT c            -> ops_c c
    | SetThT s           -> ops_st s
    | SetElemT s         -> ops_se s
    | PathT p            -> ops_p p
    | MemT m             -> ops_m m
    | TidArrayT tt       -> ops_tt tt
    | BucketArrayT bb    -> ops_bb bb
    | IntT i             -> ops_i i
    | MarkT m            -> ops_mk m
    | BucketT b          -> ops_b b
    | LockT l            -> ops_l l
    | LockArrayT ll      -> ops_ll ll
    | VarUpdate (_,t,tr) -> list_union [ops_t t;ops_term tr] in


  let ops_fs = Formula.make_fold
                 Formula.GenericLiteralFold
                 (fun _ a -> ops_atom a)
                 (fun _ -> empty)
                 union in

  let ops_f (phi:formula) : OpsSet.t =
    Formula.formula_fold ops_fs () phi

  in
    OpsSet.elements (ops_f phi)


(*****************************)
(**                         **)
(** Normalization functions **)
(**                         **)
(*****************************)


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
and is_var_bucket (b:bucket) : bool =
  match b with
  | VarBucket(_) -> true
  | _            -> false
and is_var_lock (l:lock) : bool =
  match l with
  | VarLock(_) -> true
  | _          -> false
and is_var_mark (m:mark) : bool =
  match m with
  | VarMark(_) -> true
  | _          -> false
and is_var_bucketarr (bb:bucketarr) : bool =
  match bb with
  | VarBucketArray(_) -> true
  | _               -> false
and is_var_lockarr (ll:lockarr) : bool =
  match ll with
  | VarLockArray(_) -> true
  | _               -> false
and is_var_tidarr (tt:tidarr) : bool =
  match tt with
  | VarTidArray(_) -> true
  | _              -> false



let is_var_term (t:term) : bool =
  match t with
  | VarT(_)          -> true
  | SetT(s)          -> is_var_set s
  | ElemT(e)         -> is_var_elem e
  | TidT(t)          -> is_var_thid t
  | AddrT(a)         -> is_var_addr a
  | CellT(c)         -> is_var_cell c
  | SetThT(st)       -> is_var_setth st
  | SetElemT(st)     -> is_var_setelem st
  | PathT(p)         -> is_var_path p
  | MemT(m)          -> is_var_mem m
  | IntT(i)          -> is_var_int i
  | TidArrayT(tt)    -> is_var_tidarr tt
  | LockArrayT(ll)   -> is_var_lockarr ll
  | BucketArrayT(bb) -> is_var_bucketarr bb
  | LockT(l)         -> is_var_lock l
  | BucketT(b)       -> is_var_bucket b
  | MarkT(m)         -> is_var_mark m
  | VarUpdate _      -> false


let make_compatible_term_from_var (t:term) (v:V.t) : term =
  match t with
  | VarT _         -> VarT v
  | SetT _         -> SetT         (VarSet v)
  | ElemT _        -> ElemT        (VarElem v)
  | TidT _         -> TidT         (VarTh v)
  | AddrT _        -> AddrT        (VarAddr v)
  | CellT _        -> CellT        (VarCell v)
  | SetThT _       -> SetThT       (VarSetTh v)
  | SetElemT _     -> SetElemT     (VarSetElem v)
  | PathT _        -> PathT        (VarPath v)
  | MemT _         -> MemT         (VarMem v)
  | IntT _         -> IntT         (VarInt v)
  | TidArrayT _    -> TidArrayT    (VarTidArray v)
  | BucketArrayT _ -> BucketArrayT (VarBucketArray v)
  | MarkT _        -> MarkT        (VarMark v)
  | BucketT _      -> BucketT      (VarBucket v)
  | LockT _        -> LockT        (VarLock v)
  | LockArrayT _   -> LockArrayT   (VarLockArray v)
  | VarUpdate _  -> assert false


let term_to_var (t:term) : V.t =
  match t with
  | VarT v -> v
  | SetT         (VarSet v)         -> V.set_sort v Set
  | ElemT        (VarElem v)        -> V.set_sort v Elem
  | TidT         (VarTh v)          -> V.set_sort v Tid
  | AddrT        (VarAddr v)        -> V.set_sort v Addr
  | CellT        (VarCell v)        -> V.set_sort v Cell
  | SetThT       (VarSetTh v)       -> V.set_sort v SetTh
  | SetElemT     (VarSetElem v)     -> V.set_sort v SetElem
  | PathT        (VarPath v)        -> V.set_sort v Path
  | MemT         (VarMem v)         -> V.set_sort v Mem
  | IntT         (VarInt v)         -> V.set_sort v Int
  | TidArrayT    (VarTidArray v)    -> V.set_sort v TidArray
  | BucketArrayT (VarBucketArray v) -> V.set_sort v BucketArray
  | MarkT        (VarMark v)        -> V.set_sort v Mark
  | BucketT      (VarBucket v)      -> V.set_sort v Bucket
  | LockT        (VarLock v)        -> V.set_sort v Lock
  | LockArrayT   (VarLockArray v)   -> V.set_sort v LockArray
  | _                               -> raise(No_variable_term t)





module NOpt = struct
                module VS = V
                type norm_atom = atom
                type norm_term = term
                type norm_formula = formula
                let norm_varset = varset
                let norm_fresh_vinfo = (fun _ -> {treat_as_pc=false})
                let norm_fresh_vname = sort_to_str
              end

module THMNorm = Normalization.Make(NOpt)



let rec norm_literal (info:THMNorm.t) (l:literal) : formula =
  let append_if_diff (t:term) (v:V.t) : unit =
    if is_var_term t then
      (if (term_to_var t) <> v then THMNorm.add_term_map info t v)
    else
      THMNorm.add_term_map info t v in
  let gen_if_not_var (t:term) (s:sort) : V.t =
    if is_var_term t then
      term_to_var t
    else try
           try
             THMNorm.find_proc_term info t
           with _ -> THMNorm.find_term_map info t
         with _ -> begin
                     let v = THMNorm.gen_fresh_var info s in
                     append_if_diff t v;
                     v
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
    | AddrToSet (m,a) -> AddrToSet (norm_mem m, norm_addr a)
    | BucketRegion (b) -> let b_var = gen_if_not_var (BucketT b) Bucket in
                            BucketRegion(norm_bucket (VarBucket b_var))

  and norm_tid (t:tid) : tid =
    match t with
    | VarTh v -> VarTh v
    | NoTid -> NoTid
    | CellLockId (c) -> CellLockId (norm_cell c)
    | BucketTid (b) -> let b_var = gen_if_not_var (BucketT b) Bucket in
                        BucketTid(norm_bucket (VarBucket b_var))
    | TidArrRd _ -> let t_var = gen_if_not_var (TidT t) Tid in
                      VarTh t_var
    | LockId (l) -> LockId (norm_lock l)

  and norm_elem (e:elem) : elem =
    match e with
    | VarElem v -> VarElem v
    | CellData c -> CellData (norm_cell c)
    | HavocListElem -> HavocListElem
    | LowestElem -> LowestElem
    | HighestElem -> HighestElem

  and norm_addr (a:addr) : addr =
    match a with
    | VarAddr v -> VarAddr v
    | Null -> Null
    | Next (c) -> Next (norm_cell c)
    | FirstLocked (m,p) -> FirstLocked(norm_mem m, norm_path p)
    | LastLocked (m,p) -> LastLocked(norm_mem m, norm_path p)
    | BucketInit (b) -> let b_var = gen_if_not_var (BucketT b) Bucket in
                          BucketInit(norm_bucket (VarBucket b_var))
    | BucketEnd (b) -> let b_var = gen_if_not_var (BucketT b) Bucket in
                          BucketEnd(norm_bucket (VarBucket b_var))

  and norm_cell (c:cell) : cell =
    match c with
    | VarCell v -> VarCell v
    | Error -> Error
    | MkCell (e,a,t) -> MkCell(norm_elem e, norm_addr a, norm_tid t)
    | MkCellMark (e,a,t,m) -> MkCellMark(norm_elem e, norm_addr a,
                                         norm_tid t, norm_mark m)
    | CellLock (c,t) -> CellLock (norm_cell c, norm_tid t)
    | CellUnlock (c) -> CellUnlock (norm_cell c)
    | CellAt (m,a) -> CellAt (norm_mem m, norm_addr a)

  and norm_lock (l:lock) : lock =
    match l with
    | VarLock v -> VarLock v
    | MkLock (t) -> MkLock(norm_tid t)
    | LLock (l,t) -> LLock(norm_lock l, norm_tid t)
    | LUnlock (l) -> LUnlock(norm_lock l)
    | LockArrRd _ -> let l_var = gen_if_not_var (LockT l) Lock in
                       VarLock l_var

  and norm_mark (m:mark) : mark =
    match m with
    | VarMark v -> VarMark v
    | MarkTrue -> MarkTrue
    | MarkFalse -> MarkFalse
    | Marked c -> Marked (norm_cell c)

  and norm_bucket (b:bucket) : bucket =
    match b with
    | VarBucket v -> VarBucket v
    | MkBucket _ -> let b_var = gen_if_not_var (BucketT b) Bucket in
                      VarBucket b_var
    | BucketArrRd _ -> let b_var = gen_if_not_var (BucketT b) Bucket in
                         VarBucket b_var

  and norm_setth (s:setth) : setth =
    match s with
    | VarSetTh v -> VarSetTh v
    | EmptySetTh -> EmptySetTh
    | SinglTh t -> SinglTh (norm_tid t)
    | UnionTh (s1,s2) -> UnionTh (norm_setth s1, norm_setth s2)
    | IntrTh (s1,s2) -> IntrTh (norm_setth s1, norm_setth s2)
    | SetdiffTh (s1,s2) -> SetdiffTh (norm_setth s1, norm_setth s2)
    | LockSet (m,p) -> LockSet(norm_mem m, norm_path p)

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
    | GetPath (m,a1,a2) -> GetPath (norm_mem m, norm_addr a1, norm_addr a2)

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
    | IntMod (j1,j2) -> IntMod (j1,j2)
    | HashCode (e) -> HashCode (norm_elem e)

  and norm_bucketarr (bb:bucketarr) : bucketarr =
    match bb with
    | VarBucketArray v -> VarBucketArray v
    | BucketArrayUp (cc,i,b) -> let i_var = gen_if_not_var (IntT i) Int in
                                  BucketArrayUp (norm_bucketarr cc, VarInt i_var,
                                                 norm_bucket b)

  and norm_tidarr (tt:tidarr) : tidarr =
    match tt with
    | VarTidArray v -> VarTidArray v
    | TidArrayUp (yy,i,t) -> let i_var = gen_if_not_var (IntT i) Int in
                                TidArrayUp (norm_tidarr yy, VarInt i_var, norm_tid t)

  and norm_lockarr (ll:lockarr) : lockarr =
    match ll with
    | VarLockArray v -> VarLockArray v
    | LockArrayUp (mm,i,l) -> let i_var = gen_if_not_var (IntT i) Int in
                                LockArrayUp (norm_lockarr mm, VarInt i_var,
                                             norm_lock l)

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
    | TidArrayT tt -> TidArrayT (norm_tidarr tt)
    | BucketArrayT bb -> BucketArrayT (norm_bucketarr bb)
    | MarkT m -> MarkT (norm_mark m)
    | BucketT b -> BucketT (norm_bucket b)
    | LockT l -> LockT (norm_lock l)
    | LockArrayT ll -> LockArrayT (norm_lockarr ll)
    | VarUpdate (v,th,t) -> VarUpdate (v, norm_tid th, norm_term t)


  and norm_atom (a:atom) : atom =
    match a with
    | Append (p1,p2,p3) -> Append (norm_path p1, norm_path p2, norm_path p3)
    | Reach (m,a1,a2,p) -> Reach (norm_mem m, norm_addr a1, norm_addr a2,
                                  norm_path p)
    | OrderList (m,a1,a2) -> OrderList (norm_mem m, norm_addr a1, norm_addr a2)
    | Hashmap(m,s,se,bb,i) -> let i_var = gen_if_not_var (IntT i) Int in
                                Hashmap(norm_mem m, norm_set s, norm_setelem se,
                                        norm_bucketarr bb, VarInt i_var)
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
    (* Equality between bucket variable and bucket array *)
    | Eq (BucketT (VarBucket b), BucketT (BucketArrRd(bb,i)))
    | Eq (BucketT (BucketArrRd(bb,i)), BucketT (VarBucket b)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          Eq (BucketT (VarBucket b),
              BucketT (BucketArrRd(norm_bucketarr bb, VarInt i_var)))
    (* Inequality between bucket variable and bucket array *)
    | InEq (BucketT (VarBucket b), BucketT (BucketArrRd(bb,i)))
    | InEq (BucketT (BucketArrRd(bb,i)), BucketT (VarBucket b)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          InEq (BucketT (VarBucket b),
                BucketT (BucketArrRd(norm_bucketarr bb,VarInt i_var)))
    (* Equality between lock variable and lock array *)
    | Eq (LockT (VarLock l), LockT (LockArrRd(ll,i)))
    | Eq (LockT (LockArrRd(ll,i)), LockT (VarLock l)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          Eq (LockT (VarLock l),
              LockT (LockArrRd(norm_lockarr ll, VarInt i_var)))
    (* Inequality between lock variable and lock array *)
    | InEq (LockT (VarLock l), LockT (LockArrRd(ll,i)))
    | InEq (LockT (LockArrRd(ll,i)), LockT (VarLock l)) ->
        let i_var = gen_if_not_var (IntT i) Int in
          InEq (LockT (VarLock l),
                LockT (LockArrRd(norm_lockarr ll,VarInt i_var)))
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
    (* Equality between address and binit *)
    | Eq (AddrT a, AddrT(BucketInit b))
    | Eq (AddrT(BucketInit b), AddrT a) ->
        let b' = gen_if_not_var (BucketT b) Bucket in
        let a' = gen_if_not_var (AddrT a) Addr in
        let e = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let s = VarSet (THMNorm.gen_fresh_var info Set) in
        let t = VarTh (THMNorm.gen_fresh_var info Tid) in
          Eq(BucketT(VarBucket b'), BucketT(MkBucket(VarAddr a',e,s,t)))
    (* Equality between address and bend *)
    | Eq (AddrT e, AddrT(BucketEnd b))
    | Eq (AddrT(BucketEnd b), AddrT e) ->
        let b' = gen_if_not_var (BucketT b) Bucket in
        let e' = gen_if_not_var (AddrT e) Addr in
        let a = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let s = VarSet (THMNorm.gen_fresh_var info Set) in
        let t = VarTh (THMNorm.gen_fresh_var info Tid) in
          Eq(BucketT(VarBucket b'), BucketT(MkBucket(a,VarAddr e',s,t)))
    (* Equality between set and breg *)
    | Eq (SetT s, SetT(BucketRegion b))
    | Eq (SetT(BucketRegion b), SetT s) ->
        let b' = gen_if_not_var (BucketT b) Bucket in
        let s' = gen_if_not_var (SetT s) Set in
        let a = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let e = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let t = VarTh (THMNorm.gen_fresh_var info Tid) in
          Eq(BucketT(VarBucket b'), BucketT(MkBucket(a,e,VarSet s',t)))
    (* Equality between thread identifier and btid *)
    | Eq (TidT t, TidT(BucketTid b))
    | Eq (TidT(BucketTid b), TidT t) ->
        let b' = gen_if_not_var (BucketT b) Bucket in
        let t' = gen_if_not_var (TidT t) Tid in
        let a = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let e = VarAddr (THMNorm.gen_fresh_var info Addr) in
        let s = VarSet (THMNorm.gen_fresh_var info Set) in
          Eq(BucketT(VarBucket b'), BucketT(MkBucket(a,e,s,VarTh t')))
    (* General equalities and inequalities *)
    | Eq (t1,t2) -> Eq (norm_term t1, norm_term t2)
    | InEq (t1,t2) -> InEq (norm_term t1, norm_term t2)
    | BoolVar v -> BoolVar v
    | PC (i,topt,pr) -> let norm_topt = match topt with
                                        | V.Shared -> V.Shared
                                        | V.Local t -> V.Local t in
                        PC (i, norm_topt, pr)
    | PCUpdate (i,t) -> PCUpdate (i, norm_tid t)
    | PCRange (i,j,topt,pr) -> let norm_topt = match topt with
                                              | V.Shared -> V.Shared
                                              | V.Local t -> V.Local t in
                               PCRange (i, j, norm_topt, pr)

  in
  match l with
  | F.Atom a -> F.Literal(F.Atom (norm_atom a))
  | F.NegAtom a -> F.Literal(F.NegAtom (norm_atom a))


and norm_formula (info:THMNorm.t) (phi:formula) : formula =
  match phi with
  | F.Literal(F.Atom(InEq(CellT c1, CellT c2))) ->
      norm_formula info (F.Or(F.atom_to_formula (InEq(ElemT(CellData c1),
                                                      ElemT(CellData c2))),
                         F.Or(F.atom_to_formula (InEq(AddrT(Next c1),
                                                      AddrT(Next c2))),
                              F.atom_to_formula (InEq(TidT(CellLockId c1),
                                                      TidT(CellLockId c2))))))
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


(* FORMULA NORMALIZATION *)
let normalize (phi:formula) : formula =
    (* Create a new normalization *)
    let norm_info = THMNorm.new_norm phi in
    (* Process the original formula *)
    let phi' = norm_formula norm_info (F.nnf phi) in
    (* Normalize all remaining literals stored in the normalization table *)
    verbl _LONG_INFO "WILL NORMALIZE REMAINING ELEMENTS";
    let lit_list = ref [] in
    while (THMNorm.term_map_size norm_info > 0) do
      THMNorm.iter_term_map (fun t v ->
        THMNorm.add_proc_term_map norm_info t v;
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
        lit_list := lit_to_add :: !lit_list;
        THMNorm.remove_term_map norm_info t
      ) norm_info
    done;
    if !lit_list = [] then
      phi'
    else
      F.And (F.conj_list !lit_list, phi')
