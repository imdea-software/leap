open Printf
open LeapLib


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
  | Mark
  | Unknown

type var_info_t =
  {
    mutable smp_interesting : bool;
    treat_as_pc : bool;
  }

module V = Variable.Make (
  struct
    type sort_t = sort
    type info_t = var_info_t
  end )

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
  | MarkT    of mark
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
  | LastLocked of mem * path
(*  | Malloc of elem * addr * tid *)
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

exception WrongType of term
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
  V.build id s pr th p {smp_interesting=false; treat_as_pc= treat_as_pc;} ~fresh:fresh


let treat_as_pc (v:V.t) : bool =
  (V.info v).treat_as_pc


let variable_mark_smp_interesting (v:V.t) (b:bool) : unit =
  (V.info v).smp_interesting <- b


let variable_is_smp_interesting (v:V.t) : bool =
  (V.info v).smp_interesting


let is_primed_tid (th:tid) : bool =
  match th with
  | VarTh v           -> V.is_primed v
  | NoTid             -> false
  | CellLockId _      -> false
  (* FIX: Propagate the query inside cell??? *)


(*******************************)
(*    SMP MARKING FUNCTIONS    *)
(*******************************)
let addr_mark_smp_interesting (a:addr) (b:bool) : unit =
  match a with
  | VarAddr v -> variable_mark_smp_interesting v b
  | _         -> ()


let tid_mark_smp_interesting (t:tid) (b:bool) : unit =
  match t with
  | VarTh v -> variable_mark_smp_interesting v b
  | _       -> ()

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


let unify_var_info (info1:var_info_t) (info2:var_info_t) : var_info_t =
  {
    smp_interesting = (info1.smp_interesting || info2.smp_interesting);
    treat_as_pc = (info1.treat_as_pc || info2.treat_as_pc);
  }


let unify_varset (s:V.VarSet.t) : V.VarSet.t =
  let tbl = Hashtbl.create (V.VarSet.cardinal s) in
  V.VarSet.iter (fun v ->
    let base = (V.id v, V.sort v, V.is_primed v,
                V.parameter v, V.scope v) in
    if Hashtbl.mem tbl base then
      let prev_info = Hashtbl.find tbl base in
      Hashtbl.replace tbl base (unify_var_info (V.info v) prev_info)
    else
      Hashtbl.add tbl base (V.info v)
  ) s;
  Hashtbl.fold (fun (id,s,pr,th,p) _ set ->
    let new_var = build_var id s pr th p
    in
      V.VarSet.add new_var set
  ) tbl V.VarSet.empty


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
and get_varset_int i =
  match i with
      IntVal _ -> V.VarSet.empty
    | VarInt v -> V.VarSet.singleton v @@ get_varset_from_param v
    | IntNeg j -> get_varset_int j
    | IntAdd (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntSub (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntMul (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
    | IntDiv (j1,j2) -> (get_varset_int j1) @@ (get_varset_int j2)
and get_varset_tid th =
  match th with
      VarTh v      -> V.VarSet.singleton v @@ get_varset_from_param v
    | NoTid       -> V.VarSet.empty
    | CellLockId c ->  get_varset_cell c
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
    | Emp                -> V.VarSet.empty
    | Update(m,a,c)      -> (get_varset_mem m) @@ (get_varset_addr a) @@ (get_varset_cell c)
and get_varset_atom a =
  match a with
      Append(p1,p2,p3)       -> (get_varset_path p1) @@ (get_varset_path p2) @@
                                (get_varset_path p3)
    | Reach(m,a1,a2,p)       -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                (get_varset_addr a2) @@ (get_varset_path p)
    | OrderList(m,a1,a2)     -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                (get_varset_addr a2)
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
    | Eq((x,y))              -> (get_varset_term x) @@ (get_varset_term y)
    | InEq((x,y))            -> (get_varset_term x) @@ (get_varset_term y)
    | BoolVar v              -> V.VarSet.singleton v
    | PC(_,th,_)             -> (match th with
                                 | V.Shared -> V.VarSet.empty
                                 | V.Local t -> V.VarSet.singleton t)
    | PCUpdate (_,th)        -> (get_varset_tid th)
    | PCRange(_,_,th,_)      -> (match th with
                                 | V.Shared -> V.VarSet.empty
                                 | V.Local t -> V.VarSet.singleton t)
and get_varset_term t = match t with
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
    | IntT   i            -> get_varset_int i
    | MarkT  m            -> get_varset_mark m
    | VarUpdate(v,_,t)    -> (V.VarSet.singleton v) @@ (get_varset_term t) @@
                             (get_varset_from_param v)

let varset_fs = Formula.make_fold
                  Formula.GenericLiteralFold
                  (fun _ a -> get_varset_atom a)
                  (fun _ -> V.VarSet.empty)
                  V.VarSet.union


let get_varset_from_literal (l:literal) : V.VarSet.t =
  unify_varset (Formula.literal_fold varset_fs () l)


let get_varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
  unify_varset (Formula.conjunctive_formula_fold varset_fs () cf)

  
let get_varset_from_formula (phi:formula) : V.VarSet.t =
  unify_varset (Formula.formula_fold varset_fs () phi)


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


let get_termset_atom (a:atom) : TermSet.t =
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
    | Mark    -> (match t with | MarkT _    -> true | _ -> false)
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
    | MarkT _          -> Mark
    | VarUpdate(v,_,_) -> (V.sort v)
  
let terms_same_type a b =
  (get_sort_from_term a) = (get_sort_from_term b)

let is_ineq_normalized a b =
  (terms_same_type a b) && (is_term_var a && is_term_var b)

let is_eq_normalized a b =
  (terms_same_type a b) && (is_term_var a || is_term_var b)

(* TODO: propagate equalities of vars x = y *)
let rec is_term_flat t =
  match t with
      VarT(_)     -> true
    | SetT s      -> is_set_flat s
    | ElemT e     -> is_elem_flat   e
    | TidT k      -> is_tid_flat k
    | AddrT a     -> is_addr_flat a
    | CellT c     -> is_cell_flat c
    | SetThT st   -> is_setth_flat st
    | SetElemT se -> is_setelem_flat se
    | PathT p     -> is_path_flat p
    | MemT  m     -> is_mem_flat m
    | IntT i      -> is_int_flat i
    | MarkT m     -> is_mark_flat m
    | VarUpdate _ -> true

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
and is_tid_flat t =
  match t with
      VarTh _       -> true
    | NoTid        -> true     
    | CellLockId(c) -> is_cell_flat c
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
    | Emp      -> true
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

and is_atom_flat a =
  match a with
    | Append(p1,p2,p3)       -> (is_path_flat p1) && (is_path_flat p2) &&
                                (is_path_flat p3)
    | Reach(m,a1,a2,p)       -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2) && (is_path_flat p)
    | OrderList(m,a1,a2)     -> (is_mem_flat m) && (is_addr_flat a1) &&
                                (is_addr_flat a2)
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
    | Emp -> Printf.sprintf "emp"
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
and tid_to_str th =
  match th with
      VarTh(v)         -> V.to_str v
    | NoTid           -> Printf.sprintf "NoTid"
    | CellLockId(cell) -> Printf.sprintf "%s.lockid" (cell_to_str cell)
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
    | MarkT(m)           -> (mark_to_str m)
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
    | Mark    -> "Mark"
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
    | MarkT(m)           -> voc_mark m
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


and voc_addr (a:addr) : ThreadSet.t =
  match a with
    VarAddr v             -> get_tid_in v
  | Null                  -> ThreadSet.empty
  | Next(cell)            -> (voc_cell cell)
  | FirstLocked(mem,path) -> (voc_mem mem) @@ (voc_path path)
  | LastLocked(mem,path)  -> (voc_mem mem) @@ (voc_path path)


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
  | Emp                  -> ThreadSet.empty
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
    | Append (p1,p2,p3)   -> list_union [req_p p1;req_p p1;req_p p2;req_p p3]
    | Reach (m,a1,a2,p)   -> list_union [req_m m;req_a a1;req_a a2;req_p p]
    | OrderList (m,a1,a2) -> list_union [req_m m;req_a a1;req_a a2]
    | In (a,s)            -> list_union [req_a a;req_s s]
    | SubsetEq (s1,s2)    -> list_union [req_s s1;req_s s2]
    | InTh (t,s)          -> list_union [req_t t;req_st s]
    | SubsetEqTh (s1,s2)  -> list_union [req_st s1;req_st s2]
    | InElem (e,s)        -> list_union [req_e e;req_se s]
    | SubsetEqElem (s1,s2)-> list_union [req_se s1;req_se s2]
    | Less (i1,i2)        -> list_union [req_i i1; req_i i2]
    | LessEq (i1,i2)      -> list_union [req_i i1; req_i i2]
    | Greater (i1,i2)     -> list_union [req_i i1; req_i i2]
    | GreaterEq (i1,i2)   -> list_union [req_i i1; req_i i2]
    | LessElem  (e1,e2)   -> list_union [req_e e1; req_e e2]
    | GreaterElem (e1,e2) -> list_union [req_e e1; req_e e2]
    | Eq (t1,t2)          -> union (req_term t1) (req_term t2)
    | InEq (t1,t2)        -> union (req_term t1) (req_term t2)
    | BoolVar _           -> single Bool
    | PC _                -> empty
    | PCUpdate _          -> empty
    | PCRange _           -> empty

  and req_m (m:mem) : SortSet.t =
    match m with
    | VarMem _         -> single Mem
    | Emp              -> single Mem
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

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _         -> single Addr
    | Null              -> single Addr
    | Next c            -> append Addr [req_c c]
    | FirstLocked (m,p) -> append Addr [req_m m;req_p p]
    | LastLocked (m,p)  -> append Addr [req_m m;req_p p]

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
    | NoTid            -> single Tid
    | CellLockId c      -> append Tid [req_c c]

  and req_s (s:set) : SortSet.t =
    match s with
    | VarSet _         -> single Set
    | EmptySet         -> single Set
    | Singl a          -> append Set  [req_a a]
    | Union (s1,s2)    -> append Set [req_s s1;req_s s2]
    | Intr (s1,s2)     -> append Set [req_s s1;req_s s2]
    | Setdiff (s1,s2)  -> append Set [req_s s1;req_s s2]
    | PathToSet p      -> append Set [req_p p]
    | AddrToSet (m,a)  -> append Set [req_m m;req_a a]

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
    | MarkT m            -> req_mk m
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
    | Append (p1,p2,p3)   -> list_union [ops_p p1;ops_p p1;ops_p p2;ops_p p3]
    | Reach (m,a1,a2,p)   -> append Reachable[ops_m m;ops_a a1;ops_a a2;ops_p p]
    | OrderList (m,a1,a2) -> append OrderedList[ops_m m;ops_a a1;ops_a a2]
    | In (a,s)            -> list_union [ops_a a;ops_s s]
    | SubsetEq (s1,s2)    -> list_union [ops_s s1;ops_s s2]
    | InTh (t,s)          -> list_union [ops_t t;ops_st s]
    | SubsetEqTh (s1,s2)  -> list_union [ops_st s1;ops_st s2]
    | InElem (e,s)        -> list_union [ops_e e;ops_se s]
    | SubsetEqElem (s1,s2)-> list_union [ops_se s1;ops_se s2]
    | Less (i1,i2)        -> list_union [ops_i i1; ops_i i2]
    | LessEq (i1,i2)      -> list_union [ops_i i1; ops_i i2]
    | Greater (i1,i2)     -> list_union [ops_i i1; ops_i i2]
    | GreaterEq (i1,i2)   -> list_union [ops_i i1; ops_i i2]
    | LessElem (e1,e2)    -> append ElemOrder [ops_e e1; ops_e e2]
    | GreaterElem (e1,e2) -> append ElemOrder [ops_e e1; ops_e e2]
    | Eq (t1,t2)          -> list_union [ops_term t1;ops_term t2]
    | InEq (t1,t2)        -> list_union [ops_term t1;ops_term t2]
    | BoolVar _           -> empty
    | PC _                -> empty
    | PCUpdate _          -> empty
    | PCRange _           -> empty

  and ops_m (m:mem) : OpsSet.t =
    match m with
    | VarMem _         -> empty
    | Emp              -> empty
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

  and ops_a (a:addr) : OpsSet.t =
    match a with
    | VarAddr _         -> empty
    | Null              -> empty
    | Next c            -> list_union [ops_c c]
    | FirstLocked (m,p) -> append FstLocked [ops_m m;ops_p p]
    | LastLocked (m,p)  -> append LstLocked [ops_m m;ops_p p]

  and ops_e (e:elem) : OpsSet.t =
    match e with
    | VarElem _         -> empty
    | CellData c        -> ops_c c
    | HavocListElem     -> empty
    | LowestElem        -> empty
    | HighestElem       -> empty

  and ops_t (t:tid) : OpsSet.t =
    match t with
    | VarTh _           -> empty
    | NoTid            -> empty
    | CellLockId c      -> ops_c c

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
    | IntT i             -> ops_i i
    | MarkT m            -> ops_mk m
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



(* NOTE: I am not considering the possibility of having a1=a2 \/ a1=a3 in the formula *)
let rec get_addrs_eqs (phi:formula) : ((addr*addr) list * (addr*addr) list) =
  match phi with
  | Formula.Literal l -> get_addrs_eqs_lit l
  | Formula.And (f1,f2) -> let (es1,is1) = get_addrs_eqs f1 in
                           let (es2,is2) = get_addrs_eqs f2 in
                             (es1@es2, is1@is2)
  | Formula.Not f -> let (es,is) = get_addrs_eqs f in (is,es)
  | _ -> ([],[])

and get_addrs_eqs_conj (cf:conjunctive_formula) : ((addr*addr) list * (addr*addr) list) =
  match cf with
  | Formula.TrueConj -> ([],[])
  | Formula.FalseConj -> ([],[])
  | Formula.Conj xs -> List.fold_left (fun (es,is) l ->
                         let (es',is') = get_addrs_eqs_lit l in
                         (es@es', is@is')
                       ) ([],[]) xs

and get_addrs_eqs_lit (l:literal) : ((addr*addr) list * (addr*addr) list) =
  match l with
  | Formula.Atom a -> get_addrs_eqs_atom a
  | Formula.NegAtom a -> let (es,is) = get_addrs_eqs_atom a in (is,es)

and get_addrs_eqs_atom (a:atom) : ((addr*addr) list * (addr*addr) list) =
  match a with
  | Eq (AddrT a1, AddrT a2)   -> ([(a1,a2)],[])
  | InEq (AddrT a1, AddrT a2) -> ([],[(a1,a2)])
  | _ -> ([],[])


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

let eq_setelem (s1:setelem) (s2:setelem) : formula =
  Formula.atom_to_formula (Eq (SetElemT s1, SetElemT s2))

let eq_path (p1:path) (p2:path) : formula =
  Formula.atom_to_formula (Eq (PathT p1, PathT p2))

let eq_mem (m1:mem) (m2:mem) : formula =
  Formula.atom_to_formula (Eq (MemT m1, MemT m2))

let eq_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Eq (IntT i1, IntT i2))

let less_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Less (i1, i2))

let lesseq_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (LessEq (i1, i2))

let greater_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (Greater (i1, i2))

let greatereq_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (GreaterEq (i1, i2))

let eq_term (t1:term) (t2:term) : formula =
  Formula.atom_to_formula (Eq (t1, t2))

let ineq_set (s1:set) (s2:set) : formula =
  Formula.atom_to_formula (InEq (SetT s1, SetT s2))

let ineq_elem (e1:elem) (e2:elem) : formula =
  Formula.atom_to_formula (InEq (ElemT e1, ElemT e2))

let ineq_tid (t1:tid) (t2:tid) : formula =
  Formula.atom_to_formula (InEq (TidT t1, TidT t2))

let ineq_addr (a1:addr) (a2:addr) : formula =
  Formula.atom_to_formula (InEq (AddrT a1, AddrT a2))

let ineq_cell (c1:cell) (c2:cell) : formula =
  Formula.atom_to_formula (InEq (CellT c1, CellT c2))

let ineq_setth (s1:setth) (s2:setth) : formula =
  Formula.atom_to_formula (InEq (SetThT s1, SetThT s2))

let ineq_setelem (s1:setelem) (s2:setelem) : formula =
  Formula.atom_to_formula (InEq (SetElemT s1, SetElemT s2))

let ineq_path (p1:path) (p2:path) : formula =
  Formula.atom_to_formula (InEq (PathT p1, PathT p2))

let ineq_mem (m1:mem) (m2:mem) : formula =
  Formula.atom_to_formula (InEq (MemT m1, MemT m2))

let ineq_int (i1:integer) (i2:integer) : formula =
  Formula.atom_to_formula (InEq (IntT i1, IntT i2))

let ineq_term (t1:term) (t2:term) : formula =
  Formula.atom_to_formula (InEq (t1, t2))

let subseteq (s1:set) (s2:set) : formula =
  Formula.atom_to_formula (SubsetEq (s1,s2))

let atomlit (a:atom) : formula =
  Formula.atom_to_formula a
