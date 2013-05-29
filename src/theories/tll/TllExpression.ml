open Printf
open LeapLib

type varId = string


type variable = varId * sort * bool * tid option * string option

and sort =
    Set
  | Elem
  | Thid
  | Addr
  | Cell
  | SetTh
  | SetElem
  | Path
  | Mem
  | Bool
  | Unknown
and term =
    VarT     of variable
  | SetT     of set
  | ElemT    of elem
  | ThidT    of tid
  | AddrT    of addr
  | CellT    of cell
  | SetThT   of setth
  | SetElemT of setelem
  | PathT    of path
  | MemT     of mem
  | VarUpdate  of variable * tid * term
and eq = term * term
and diseq = term * term
and set =
    VarSet of variable
  | EmptySet
  | Singl     of addr
  | Union     of set * set
  | Intr      of set * set
  | Setdiff   of set * set
  | PathToSet of path
  | AddrToSet of mem * addr
and tid =
    VarTh of variable
  | NoThid
  | CellLockId of cell
and elem =
    VarElem of variable
  | CellData of cell
  | HavocListElem
  | LowestElem
  | HighestElem
and addr =
    VarAddr of variable
  | Null
  | Next of cell
  | FirstLocked of mem * path
(*  | Malloc of elem * addr * tid *)
and cell =
    VarCell of variable
  | Error
  | MkCell of elem * addr * tid
  | CellLock of cell * tid
  | CellUnlock of cell
  | CellAt of mem * addr
and setth =
    VarSetTh of variable
  | EmptySetTh
  | SinglTh   of tid
  | UnionTh   of setth * setth
  | IntrTh    of setth * setth
  | SetdiffTh of setth * setth
and setelem =
    VarSetElem   of variable
  | EmptySetElem
  | SinglElem    of elem
  | UnionElem    of setelem * setelem
  | IntrElem     of setelem * setelem
  | SetToElems   of set * mem
  | SetdiffElem  of setelem * setelem
and path =
    VarPath of variable
  | Epsilon
  | SimplePath of addr
  | GetPath    of mem * addr * addr 
and mem =
    VarMem of variable
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
  | LessElem     of elem * elem
  | GreaterElem  of elem * elem
  | Eq           of eq
  | InEq         of diseq
  | BoolVar      of variable
  | PC           of int * tid option * bool
  | PCUpdate     of int * tid
  | PCRange      of int * int * tid option * bool
and literal =
    Atom    of atom
  | NegAtom of atom
and conjunctive_formula =
    FalseConj
  | TrueConj
  | Conj of literal list
and formula =
    Literal   of literal
  | True
  | False
  | And     of formula * formula
  | Or      of formula * formula
  | Not     of formula
  | Implies of formula * formula
  | Iff     of formula * formula

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



(*************************)
(* VARIABLE MANIPULATION *)
(*************************)

let build_var (id:varId)
              (s:sort)
              (pr:bool)
              (th:tid option)
              (p:string option) : variable =
  (id,s,pr,th,p)


let param_var (v:variable) (th:tid) : variable =
  let (id,s,pr,_,p) = v
  in
    (id,s,pr,Some th,p)


let is_global_var (v:variable) : bool =
  let (_,_,_,_,p) = v in p = None


let get_sort (v:variable) : sort =
  let (_,s,_,_,_) = v in s


let prime_var (v:variable) : variable =
  let (id,s,_,th,p) = v in (id,s,true,th,p)


let unprime_var (v:variable) : variable =
  let (id,s,_,th,p) = v in (id,s,false,th,p)


let is_primed_var (v:variable) : bool =
  let (_,_,pr,_,_) = v in
    pr


let is_primed_tid (th:tid) : bool =
  match th with
  | VarTh v           -> is_primed_var v
  | NoThid            -> false
  | CellLockId _      -> false
  (* FIX: Propagate the query inside cell??? *)


let var_th (v:variable) : tid option =
  let (_,_,_,th,_) = v in th



(*******************************)
(* VARLIST/VARSET FOR FORMULAS *)
(*******************************)

module VarSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = variable
  end )

module S=VarSet

module VarIdSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = varId
  end )


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


let (@@) s1 s2 =
  S.union s1 s2

let get_varset_from_param (v:variable) : S.t =
  let (_,_,_,th,_) = v
  in
    match th with
      Some (VarTh t) -> S.singleton t
    | _              -> S.empty


let rec get_varset_set s =
  match s with
      VarSet v       -> S.singleton v @@ get_varset_from_param v
    | EmptySet       -> S.empty
    | Singl(a)       -> get_varset_addr a
    | Union(s1,s2)   -> (get_varset_set s1) @@ (get_varset_set s2)
    | Intr(s1,s2)    -> (get_varset_set s1) @@ (get_varset_set s2)
    | Setdiff(s1,s2) -> (get_varset_set s1) @@ (get_varset_set s2)
    | PathToSet(p)   -> get_varset_path p
    | AddrToSet(m,a) -> (get_varset_mem m) @@ (get_varset_addr a)
and get_varset_tid th =
  match th with
      VarTh v      -> S.singleton v @@ get_varset_from_param v
    | NoThid       -> S.empty
    | CellLockId c ->  get_varset_cell c
and get_varset_elem e =
  match e with
      VarElem v     -> S.singleton v @@ get_varset_from_param v
    | CellData c    -> get_varset_cell c
    | HavocListElem -> S.empty
    | LowestElem    -> S.empty
    | HighestElem   -> S.empty
and get_varset_addr a =
  match a with
      VarAddr v        -> S.singleton v @@ get_varset_from_param v
    | Null             -> S.empty
    | Next c           -> get_varset_cell c
    | FirstLocked(m,p) -> (get_varset_mem m) @@ (get_varset_path p)
(*    | Malloc(e,a,th)   -> (get_varset_elem e) @@ (get_varset_addr a) @@  (get_varset_tid th) *)
and get_varset_cell c = match c with
      VarCell v      -> S.singleton v @@ get_varset_from_param v
    | Error          -> S.empty
    | MkCell(e,a,th) -> (get_varset_elem e) @@ (get_varset_addr a) @@ (get_varset_tid th)
    | CellLock(c,th)    ->  (get_varset_cell c) @@ (get_varset_tid th)
    | CellUnlock(c)  ->  get_varset_cell c
    | CellAt(m,a)    ->  (get_varset_mem  m) @@ (get_varset_addr a)
and get_varset_setth sth =
  match sth with
      VarSetTh v         -> S.singleton v @@ get_varset_from_param v
    | EmptySetTh         -> S.empty
    | SinglTh(th)        -> (get_varset_tid th)
    | UnionTh(st1,st2)   -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | IntrTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
    | SetdiffTh(st1,st2) -> (get_varset_setth st1) @@ (get_varset_setth st2)
and get_varset_setelem se =
  match se with
      VarSetElem v         -> S.singleton v @@ get_varset_from_param v
    | EmptySetElem         -> S.empty
    | SinglElem(e)         -> (get_varset_elem e)
    | UnionElem(st1,st2)   -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | IntrElem(st1,st2)    -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
    | SetToElems(s,m)      -> (get_varset_set s) @@ (get_varset_mem m)
    | SetdiffElem(st1,st2) -> (get_varset_setelem st1) @@ (get_varset_setelem st2)
and get_varset_path p =
  match p with
      VarPath v          -> S.singleton v @@ get_varset_from_param v
    | Epsilon            -> S.empty
    | SimplePath(a)      -> (get_varset_addr a)
    | GetPath(m,a1,a2)   -> (get_varset_mem m) @@ (get_varset_addr a1) @@ (get_varset_addr a2)
and get_varset_mem m =
  match m with
      VarMem v           -> S.singleton v @@ get_varset_from_param v
    | Emp                -> S.empty
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
    | LessElem(e1,e2)        -> (get_varset_elem e1) @@ (get_varset_elem e2)
    | GreaterElem(e1,e2)     -> (get_varset_elem e1) @@ (get_varset_elem e2)
    | Eq((x,y))              -> (get_varset_term x) @@ (get_varset_term y)
    | InEq((x,y))            -> (get_varset_term x) @@ (get_varset_term y)
    | BoolVar v              -> S.singleton v
    | PC(pc,th,pr)           -> Option.map_default get_varset_tid S.empty th
    | PCUpdate (pc,th)       -> (get_varset_tid th)
    | PCRange(pc1,pc2,th,pr) -> Option.map_default get_varset_tid S.empty th
and get_varset_term t = match t with
      VarT   v            -> S.singleton v @@ get_varset_from_param v
    | SetT   s            -> get_varset_set s
    | ElemT  e            -> get_varset_elem e
    | ThidT  th           -> get_varset_tid th
    | AddrT  a            -> get_varset_addr a
    | CellT  c            -> get_varset_cell c
    | SetThT st           -> get_varset_setth st
    | SetElemT se         -> get_varset_setelem se
    | PathT  p            -> get_varset_path p
    | MemT   m            -> get_varset_mem m
    | VarUpdate(v,pc,t)   -> (S.singleton v) @@ (get_varset_term t) @@
                             (get_varset_from_param v)
and get_varset_literal l =
  match l with
      Atom a    -> get_varset_atom a
    | NegAtom a -> get_varset_atom a

and get_varset_from_conj phi =
  let another_lit vars alit = vars @@ (get_varset_literal alit) in
  match phi with
      TrueConj   -> S.empty
    | FalseConj  -> S.empty
    | Conj l     -> List.fold_left (another_lit) S.empty l

and get_varset_from_formula phi =
  match phi with
    Literal l       -> get_varset_literal l
  | True            -> S.empty
  | False           -> S.empty
  | And (f1,f2)     -> (get_varset_from_formula f1) @@
                       (get_varset_from_formula f2)
  | Or (f1,f2)      -> (get_varset_from_formula f1) @@
                       (get_varset_from_formula f2)
  | Not f           -> (get_varset_from_formula f)
  | Implies (f1,f2) -> (get_varset_from_formula f1) @@
                       (get_varset_from_formula f2)
  | Iff (f1,f2)     -> (get_varset_from_formula f1) @@
                       (get_varset_from_formula f2)


let localize_with_underscore (v:varId) (p_name:string option) : string =
  let p_str = Option.map_default (fun p -> p^"_") "" p_name
  in
    sprintf "%s%s" p_str v


let varset_of_sort all s =
  let filt (v,asort,pr,th,p) res =
    if asort=s then
      VarSet.add (v,asort,pr,None,p) res
(*      VarSet.add ((localize_with_underscore v p) res *)
    else
      res in
    S.fold filt all VarSet.empty

let get_varset_of_sort_from_conj phi s =
  varset_of_sort (get_varset_from_conj phi) s


let get_varlist_from_conj phi =
  S.elements (get_varset_from_conj phi)

let varlist_of_sort varlist s =
  let is_s (_,asort,_,_,_) = (asort=s) in
  List.map (fun (v,_,_,_,p) -> (localize_with_underscore v p))
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
  | InTh(th,st)            -> add_list [ThidT th; SetThT st]
  | SubsetEqTh(st1,st2)    -> add_list [SetThT st1; SetThT st2]
  | InElem(e,se)           -> add_list [ElemT e; SetElemT se]
  | SubsetEqElem(se1,se2)  -> add_list [SetElemT se1; SetElemT se2]
  | LessElem(e1,e2)        -> add_list [ElemT e1; ElemT e2]
  | GreaterElem(e1,e2)     -> add_list [ElemT e1; ElemT e2]
  | Eq((x,y))              -> add_list [x;y]
  | InEq((x,y))            -> add_list [x;y]
  | BoolVar v              -> add_list [VarT v]
  | PC(pc,th,pr)           -> (match th with
                               | None   -> TermSet.empty
                               | Some t -> add_list [ThidT t])
  | PCUpdate (pc,th)       -> add_list [ThidT th]
  | PCRange(pc1,pc2,th,pr) -> (match th with
                               | None   -> TermSet.empty
                               | Some t -> add_list [ThidT t])

and get_termset_literal (l:literal) : TermSet.t =
  match l with
  | Atom a    -> get_termset_atom a
  | NegAtom a -> get_termset_atom a

and get_termset_from_conjformula (cf:conjunctive_formula) : TermSet.t =
  match cf with
  | TrueConj  -> TermSet.empty
  | FalseConj -> TermSet.empty
  | Conj ls   -> List.fold_left (fun set l ->
                   TermSet.union set (get_termset_literal l)
                 ) TermSet.empty ls

and get_termset_from_formula (phi:formula) : TermSet.t =
  match phi with
  | Literal l       -> get_termset_literal l
  | True            -> TermSet.empty
  | False           -> TermSet.empty
  | And (f1,f2)     -> TermSet.union (get_termset_from_formula f1)
                                     (get_termset_from_formula f2)
  | Or (f1,f2)      -> TermSet.union (get_termset_from_formula f1)
                                     (get_termset_from_formula f2)
  | Not f           -> (get_termset_from_formula f)
  | Implies (f1,f2) -> TermSet.union (get_termset_from_formula f1)
                                     (get_termset_from_formula f2)
  | Iff (f1,f2)     -> TermSet.union (get_termset_from_formula f1)
                                     (get_termset_from_formula f2)


let termset_of_sort (all:TermSet.t) (s:sort) : TermSet.t =
  let match_sort (t:term) : bool =
    match s with
    | Set     -> (match t with | SetT _     -> true | _ -> false)
    | Elem    -> (match t with | ElemT _    -> true | _ -> false)
    | Thid    -> (match t with | ThidT _    -> true | _ -> false)
    | Addr    -> (match t with | AddrT _    -> true | _ -> false)
    | Cell    -> (match t with | CellT _    -> true | _ -> false)
    | SetTh   -> (match t with | SetThT _   -> true | _ -> false)
    | SetElem -> (match t with | SetElemT _ -> true | _ -> false)
    | Path    -> (match t with | PathT _    -> true | _ -> false)
    | Mem     -> (match t with | MemT _     -> true | _ -> false)
    | Bool    -> (match t with
                  | VarT v -> get_sort v = Bool
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
    | ThidT(VarTh  (_))   -> true
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

let get_sort_from_term t =
  match t with
      VarT _           -> Unknown
    | SetT _           -> Set
    | ElemT _          -> Elem
    | ThidT _          -> Thid
    | AddrT _          -> Addr
    | CellT _          -> Cell
    | SetThT _         -> SetTh
    | SetElemT _       -> SetElem
    | PathT _          -> Path
    | MemT _           -> Mem
    | VarUpdate(v,_,_) -> get_sort v
  
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
    | ThidT k     -> is_tid_flat k
    | AddrT a     -> is_addr_flat a
    | CellT c     -> is_cell_flat c
    | SetThT st   -> is_setth_flat st
    | SetElemT se -> is_setelem_flat se
    | PathT p     -> is_path_flat p
    | MemT  m     -> is_mem_flat m
    | VarUpdate _ -> true

and is_set_flat t =
  match t with
      VarSet _ -> true
    | EmptySet -> true
    | Singl(a) -> is_addr_var  a
    | Union(s1,s2) -> (is_set_var s1) && (is_set_var s2)
    | Intr(s1,s2)  -> (is_set_var s1) && (is_set_var s2)
    | Setdiff(s1,s2) -> (is_set_var s1) && (is_set_var s2)
    | PathToSet(p)   -> (is_path_var p)
    | AddrToSet(m,a) -> (is_mem_var m) && (is_addr_var a)
and is_tid_flat t =
  match t with
      VarTh _       -> true
    | NoThid        -> true     
    | CellLockId(c) -> is_cell_var c
and is_elem_flat t =
  match t with
      VarElem _     -> true
    | CellData(c)   -> is_cell_var c
    | HavocListElem -> true
    | LowestElem    -> true
    | HighestElem   -> true
and is_addr_flat t =
  match t with
      VarAddr _        -> true
    | Null             -> true
    | Next(c)          -> is_cell_var c
    | FirstLocked(m,p) -> (is_mem_var m) && (is_path_var p)
(*    | Malloc(m,a,k)    -> (is_mem_var m) && (is_addr_var a) && (is_thread_var k) *)
and is_cell_flat t =
  match t with
      VarCell _  -> true
    | Error      -> true
    | MkCell(e,a,k) -> (is_elem_var e) && (is_addr_var a) && (is_tid_var k)
    | CellLock(c,th)   -> (is_cell_var c) && (is_tid_var th)
    | CellUnlock(c) -> is_cell_var c
    | CellAt(m,a)   -> (is_mem_var m) && (is_addr_var a)
and is_setth_flat t =
  match t with
      VarSetTh _ -> true
    | EmptySetTh -> true
    | SinglTh(k)         -> (is_tid_var k)
    | UnionTh(st1,st2)   -> (is_setth_var st1) && (is_setth_var st2)
    | IntrTh(st1,st2)    -> (is_setth_var st1) && (is_setth_var st2)
    | SetdiffTh(st1,st2) -> (is_setth_var st1) && (is_setth_var st2)
and is_setelem_flat t =
  match t with
      VarSetElem _ -> true
    | EmptySetElem -> true
    | SinglElem(k)         -> (is_elem_var k)
    | UnionElem(st1,st2)   -> (is_setelem_var st1) && (is_setelem_var st2)
    | IntrElem(st1,st2)    -> (is_setelem_var st1) && (is_setelem_var st2)
    | SetToElems(s,m)      -> (is_set_var s) && (is_mem_var m)
    | SetdiffElem(st1,st2) -> (is_setelem_var st1) && (is_setelem_var st2)
and is_path_flat t =
  match t with
      VarPath _ -> true
    | Epsilon   -> true
    | SimplePath(a)    -> is_addr_var a
    | GetPath(m,a1,a2) -> (is_mem_var m) && (is_addr_var a1) && (is_addr_var a2)
and is_mem_flat t =
  match t with
      VarMem _ -> true
    | Emp      -> true
    | Update(m,a,c) -> (is_mem_var m) && (is_addr_var a) && (is_cell_var c)
  

let is_literal_flat lit =
  match lit with
      Atom a ->
  begin match a with
    | Append(p1,p2,p3)       -> (is_path_var p1) && (is_path_var p2) &&
                                (is_path_var p3)
    | Reach(m,a1,a2,p)       -> (is_mem_var m) && (is_addr_var a1) &&
                                (is_addr_var a2) && (is_path_var p)
    | OrderList(m,a1,a2)     -> (is_mem_var m) && (is_addr_var a1) &&
                                (is_addr_var a2)
    | In(a,s)                -> (is_addr_var a) && (is_set_var s)
    | SubsetEq(s1,s2)        -> (is_set_var s1) && (is_set_var s2)
    | InTh(k,st)             -> (is_tid_var k) && (is_setth_var st)
    | SubsetEqTh(st1,st2)    -> (is_setth_var st1) && (is_setth_var st2)
    | InElem(e,se)           -> (is_elem_var e) && (is_setelem_var se)
    | SubsetEqElem(se1,se2)  -> (is_setelem_var se1) && (is_setelem_var se2)
    | LessElem(e1,e2)        -> (is_elem_var e1) && (is_elem_var e2)
    | GreaterElem(e1,e2)     -> (is_elem_var e1) && (is_elem_var e2)
    | Eq(t1,t2)              -> ((is_term_var t1) && (is_term_var t2)  ||
                                 (is_term_var t1) && (is_term_flat t2)  ||
                                 (is_term_flat t1) && (is_term_var t2))
    | InEq(x,y)              -> (is_term_var x) && (is_term_var y)
    | BoolVar v              -> true
    | PC (pc,t,pr)           -> true
    | PCUpdate (pc,t)        -> true
    | PCRange (pc1,pc2,t,pr) -> true
  end
    | NegAtom a ->
  begin match a with
    | Append(p1,p2,p3)      -> (is_path_var p1) && (is_path_var p2) &&
                               (is_path_var p3)
    | Reach(m,a1,a2,p)      -> (is_mem_var m) && (is_addr_var a1) &&
                               (is_addr_var a2) && (is_path_var p)
    | OrderList(m,a1,a2)    -> (is_mem_var m) && (is_addr_var a1) &&
                               (is_addr_var a2)
    | In(a,s)               -> (is_addr_var a) && (is_set_var s)
    | SubsetEq(s1,s2)       -> (is_set_var s1) && (is_set_var s2)
    | InTh(k,st)            -> (is_tid_var k) && (is_setth_var st)
    | SubsetEqTh(st1,st2)   -> (is_setth_var st1) && (is_setth_var st2)
    | InElem(e,se)          -> (is_elem_var e) && (is_setelem_var se)
    | SubsetEqElem(se1,se2) -> (is_setelem_var se1) && (is_setelem_var se2)
    | LessElem(e1,e2)       -> (is_elem_var e1) && (is_elem_var e2)
    | GreaterElem(e1,e2)    -> (is_elem_var e1) && (is_elem_var e2)
    | Eq(x,y)               ->  (is_term_var x) && (is_term_var y)
    | InEq(t1,t2)           -> ((is_term_var  t1) && (is_term_var  t2) ||
                                (is_term_var  t1) && (is_term_flat t2) ||
                                (is_term_flat t1) && (is_term_var  t2) )
    | BoolVar v             -> true
    | PC _                  -> true
    | PCUpdate _            -> true
    | PCRange _             -> true
  end


(*******************)
(* PRETTY PRINTERS *)
(* WIHOUT FOLD     *)
(*******************)

let localize_var_id (v:varId) (p_name:string) : string =
  sprintf "%s::%s" p_name v


let rec variable_to_str (v:variable) : string =
  let (id,_,pr,th,p) = v in
  let v_str = sprintf "%s%s" (Option.map_default (localize_var_id id) id p)
                             (Option.map_default (fun t -> "(" ^ tid_to_str t ^ ")" ) "" th)
  in
    if pr then v_str ^ "'" else v_str

and atom_to_str a =
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
  | LessElem(e1,e2)            -> Printf.sprintf "%s < %s"
                                    (elem_to_str e1) (elem_to_str e2)
  | GreaterElem(e1,e2)         -> Printf.sprintf "%s < %s"
                                    (elem_to_str e1) (elem_to_str e2)
  | Eq(exp)                    -> eq_to_str (exp)
  | InEq(exp)                  -> diseq_to_str (exp)
  | BoolVar v                  -> variable_to_str v
  | PC (pc,t,pr)               -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = Option.map_default
                                                 tid_to_str "" t in
                                  Printf.sprintf "%s(%s) = %i" pc_str th_str pc
  | PCUpdate (pc,t)            -> let th_str = tid_to_str t in
                                  Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
  | PCRange (pc1,pc2,t,pr)     -> let pc_str = if pr then "pc'" else "pc" in
                                  let th_str = Option.map_default
                                                 tid_to_str "" t in
                                  Printf.sprintf "%i <= %s(%s) <= %i"
                                                  pc1 pc_str th_str pc2

and literal_to_str e =
  match e with
      Atom(a)    -> atom_to_str a 
    | NegAtom(a) -> Printf.sprintf "(~ %s)" (atom_to_str a)
and mem_to_str expr =
  match expr with
      VarMem(v) -> variable_to_str v
    | Emp -> Printf.sprintf "emp"
    | Update(mem,add,cell) -> Printf.sprintf "upd(%s,%s,%s)"
  (mem_to_str mem) (addr_to_str add) (cell_to_str cell)
and path_to_str expr =
  match expr with
      VarPath(v) -> variable_to_str v
    | Epsilon -> Printf.sprintf "epsilon"
    | SimplePath(addr) -> Printf.sprintf "[ %s ]" (addr_to_str addr)
    | GetPath(mem,add_from,add_to) -> Printf.sprintf "getp(%s,%s,%s)"
  (mem_to_str mem) (addr_to_str add_from) (addr_to_str add_to)
and set_to_str e =
  match e with
      VarSet(v)  -> variable_to_str v
    | EmptySet  -> "EmptySet"
    | Singl(addr) -> Printf.sprintf "{ %s }" (addr_to_str addr)
    | Union(s1,s2) -> Printf.sprintf "%s Union %s"
  (set_to_str s1) (set_to_str s2)
    | Intr(s1,s2) -> Printf.sprintf "%s Intr %s"
  (set_to_str s1) (set_to_str s2)
    | Setdiff(s1,s2) -> Printf.sprintf "%s SetDiff %s"
  (set_to_str s1) (set_to_str s2)
    | PathToSet(path) -> Printf.sprintf "path2set(%s)"
  (path_to_str path)
    | AddrToSet(mem,addr) -> Printf.sprintf "addr2set(%s,%s)"
  (mem_to_str mem) (addr_to_str addr)
and setth_to_str e =
  match e with
      VarSetTh(v)  -> variable_to_str v
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
      VarSetElem(v)  -> variable_to_str v
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
      VarCell(v) -> variable_to_str v
    | Error -> "Error"
    | MkCell(data,addr,th) -> Printf.sprintf "mkcell(%s,%s,%s)"
  (elem_to_str data) (addr_to_str addr) (tid_to_str th)
    | CellLock(cell,th)   -> Printf.sprintf "%s.lock(%s)"
  (cell_to_str cell) (tid_to_str th)
    | CellUnlock(cell) -> Printf.sprintf "%s.unlock"
  (cell_to_str cell)
    | CellAt(mem,addr) -> Printf.sprintf "%s [ %s ]" (mem_to_str mem) (addr_to_str addr)
and addr_to_str expr =
  match expr with
      VarAddr(v) -> variable_to_str v
    | Null    -> "null"
    | Next(cell)           -> Printf.sprintf "%s.next" (cell_to_str cell)
    | FirstLocked(mem,path) -> Printf.sprintf "firstlocked(%s,%s)"
  (mem_to_str mem) (path_to_str path)
(*    | Malloc(e,a,t)     -> Printf.sprintf "malloc(%s,%s,%s)" (elem_to_str e) (addr_to_str a) (tid_to_str t) *)
and tid_to_str th =
  match th with
      VarTh(v)         -> variable_to_str v
    | NoThid           -> Printf.sprintf "NoThid"
    | CellLockId(cell) -> Printf.sprintf "%s.lockid" (cell_to_str cell)
and eq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s = %s" (term_to_str e1) (term_to_str e2)
and diseq_to_str expr =
  let (e1,e2) = expr in
    Printf.sprintf "%s != %s" (term_to_str e1) (term_to_str e2)
and elem_to_str elem =
  match elem with
      VarElem(v)     -> variable_to_str v
    | CellData(cell) -> Printf.sprintf "%s.data" (cell_to_str cell)
    | HavocListElem  -> "havocListElem()"
    | LowestElem     -> "lowestElem"
    | HighestElem    -> "highestElem"
and term_to_str expr =
  match expr with
      VarT(v) -> variable_to_str v
    | SetT(set)          -> (set_to_str set)
    | AddrT(addr)        -> (addr_to_str addr)
    | ElemT(elem)        -> (elem_to_str elem)
    | ThidT(th)          -> (tid_to_str th)
    | CellT(cell)        -> (cell_to_str cell)
    | SetThT(setth)      -> (setth_to_str setth)
    | SetElemT(setelem)  -> (setelem_to_str setelem)
    | PathT(path)        -> (path_to_str path)
    | MemT(mem)          -> (mem_to_str mem)
    | VarUpdate (v,th,t) -> let v_str = variable_to_str v in
                            let th_str = tid_to_str th in
                            let t_str = term_to_str t in
                              Printf.sprintf "%s{%s<-%s}" v_str th_str t_str

and conjunctive_formula_to_str form =
  let rec c_to_str f str =
    match f with
  [] -> str
      | lit::sub ->
    c_to_str sub (Printf.sprintf "%s /\\ %s" str (literal_to_str lit))
  in
    match form with
      | TrueConj  -> Printf.sprintf "true"
      | FalseConj -> Printf.sprintf "false"
      | Conj([]) -> ""
      | Conj(lit :: subform) -> c_to_str subform (literal_to_str lit)
and formula_to_str form =
  match form with
      Literal(lit) -> (literal_to_str lit)
    | True  -> Printf.sprintf "true"
    | False -> Printf.sprintf "false"
    | And(f1, f2)  ->
  Printf.sprintf "(%s /\\ %s)" (formula_to_str f1) (formula_to_str f2)
    | Or(f1,f2) ->
  Printf.sprintf "(%s \\/ %s)" (formula_to_str f1) (formula_to_str f2)
    | Not(f) ->
  Printf.sprintf "(~ %s)" (formula_to_str f)
    | Implies(f1,f2) ->
  Printf.sprintf "(%s -> %s)" (formula_to_str f1) (formula_to_str f2)
    | Iff (f1,f2) ->
  Printf.sprintf "(%s <-> %s)" (formula_to_str f1) (formula_to_str f2)

let sort_to_str s =
  match s with
      Set     -> "Set"
    | Elem    -> "Elem"
    | Thid    -> "Thid"
    | Addr    -> "Addr"
    | Cell    -> "Cell"
    | SetTh   -> "SetTh"
    | SetElem -> "SetElem"
    | Path    -> "Path"
    | Mem     -> "Mem"
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
  VarIdSet.fold (fun v str -> str ^ v ^ "\n") varset ""

let typed_variable_set_to_str tvarset =
  let pr (v,s,_,_,_) str = (str ^ v ^ ": " ^ (sort_to_str s) ^ "\n") in
    S.fold pr tvarset ""

let print_variable_set varset =
  generic_printer variable_set_to_str varset

let print_typed_variable_set tvarset =
  generic_printer typed_variable_set_to_str tvarset


(* let print_eq    e = *)
(*   generic_printer eq_to_str e *)

(* let print_diseq e = *)
(*   generic_printer eq_to_str e *)


(* VOCABULARY FUNCTIONS *)
let rec voc_var (v:variable) : tid list =
  ( match get_sort v with
    | Thid -> [VarTh v]
    | _    -> []
  ) @ Option.map_default (fun x -> [x]) [] (var_th v)


and voc_term (expr:term) : tid list =
  match expr with
    | VarT v             -> voc_var v
    | SetT(set)          -> voc_set set
    | AddrT(addr)        -> voc_addr addr
    | ElemT(elem)        -> voc_elem elem
    | ThidT(th)          -> voc_tid th
    | CellT(cell)        -> voc_cell cell
    | SetThT(setth)      -> voc_setth setth
    | SetElemT(setelem)  -> voc_setelem setelem
    | PathT(path)        -> voc_path path
    | MemT(mem)          -> voc_mem mem
    | VarUpdate (v,th,t) -> (voc_var v) @ (voc_tid th) @ (voc_term t)



and voc_set (e:set) : tid list =
  match e with
    VarSet v            -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySet            -> []
  | Singl(addr)         -> (voc_addr addr)
  | Union(s1,s2)        -> (voc_set s1) @ (voc_set s2)
  | Intr(s1,s2)         -> (voc_set s1) @ (voc_set s2)
  | Setdiff(s1,s2)      -> (voc_set s1) @ (voc_set s2)
  | PathToSet(path)     -> (voc_path path)
  | AddrToSet(mem,addr) -> (voc_mem mem) @ (voc_addr addr)


and voc_addr (a:addr) : tid list =
  match a with
    VarAddr v             -> Option.map_default (fun x->[x]) [] (var_th v)
  | Null                  -> []
  | Next(cell)            -> (voc_cell cell)
  | FirstLocked(mem,path) -> (voc_mem mem) @ (voc_path path)


and voc_elem (e:elem) : tid list =
  match e with
    VarElem v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | CellData(cell)     -> (voc_cell cell)
  | HavocListElem      -> []
  | LowestElem         -> []
  | HighestElem        -> []


and voc_tid (th:tid) : tid list =
  match th with
    VarTh v            -> th :: (Option.map_default (fun x->[x]) [] (var_th v))
  | NoThid             -> []
  | CellLockId(cell)   -> (voc_cell cell)


and voc_cell (c:cell) : tid list =
  match c with
    VarCell v            -> Option.map_default (fun x->[x]) [] (var_th v)
  | Error                -> []
  | MkCell(data,addr,th) -> (voc_elem data) @
                            (voc_addr addr) @
                            (voc_tid th)
  | CellLock(cell,th)    -> (voc_cell cell) @ (voc_tid th)
  | CellUnlock(cell)     -> (voc_cell cell)
  | CellAt(mem,addr)     -> (voc_mem mem) @ (voc_addr addr)


and voc_setth (s:setth) : tid list =
  match s with
    VarSetTh v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySetTh          -> []
  | SinglTh(th)         -> (voc_tid th)
  | UnionTh(s1,s2)      -> (voc_setth s1) @ (voc_setth s2)
  | IntrTh(s1,s2)       -> (voc_setth s1) @ (voc_setth s2)
  | SetdiffTh(s1,s2)    -> (voc_setth s1) @ (voc_setth s2)


and voc_setelem (s:setelem) : tid list =
  match s with
    VarSetElem v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySetElem          -> []
  | SinglElem(e)          -> (voc_elem e)
  | UnionElem(s1,s2)      -> (voc_setelem s1) @ (voc_setelem s2)
  | IntrElem(s1,s2)       -> (voc_setelem s1) @ (voc_setelem s2)
  | SetdiffElem(s1,s2)    -> (voc_setelem s1) @ (voc_setelem s2)
  | SetToElems(s,m)       -> (voc_set s) @ (voc_mem m)


and voc_path (p:path) : tid list =
  match p with
    VarPath v                -> Option.map_default (fun x->[x]) [] (var_th v)
  | Epsilon                  -> []
  | SimplePath(addr)         -> (voc_addr addr)
  | GetPath(mem,a_from,a_to) -> (voc_mem mem) @
                                (voc_addr a_from) @
                                (voc_addr a_to)


and voc_mem (m:mem) : tid list =
  match m with
    VarMem v             -> Option.map_default (fun x->[x]) [] (var_th v)
  | Emp                  -> []
  | Update(mem,add,cell) -> (voc_mem mem) @ (voc_addr add) @ (voc_cell cell)


and voc_atom (a:atom) : tid list =
  match a with
    Append(p1,p2,pres)         -> (voc_path p1) @
                                  (voc_path p2) @
                                  (voc_path pres)
  | Reach(h,add_from,add_to,p) -> (voc_mem h) @
                                  (voc_addr add_from) @
                                  (voc_addr add_to) @
                                  (voc_path p)
  | OrderList(h,a_from,a_to)   -> (voc_mem h) @
                                  (voc_addr a_from) @
                                  (voc_addr a_to)
  | In(a,s)                    -> (voc_addr a) @ (voc_set s)
  | SubsetEq(s_in,s_out)       -> (voc_set s_in) @ (voc_set s_out)
  | InTh(th,s)                 -> (voc_tid th) @ (voc_setth s)
  | SubsetEqTh(s_in,s_out)     -> (voc_setth s_in) @ (voc_setth s_out)
  | InElem(e,s)                -> (voc_elem e) @ (voc_setelem s)
  | SubsetEqElem(s_in,s_out)   -> (voc_setelem s_in) @ (voc_setelem s_out)
  | LessElem(e1,e2)            -> (voc_elem e1) @ (voc_elem e2)
  | GreaterElem(e1,e2)         -> (voc_elem e1) @ (voc_elem e2)
  | Eq(exp)                    -> (voc_eq exp)
  | InEq(exp)                  -> (voc_ineq exp)
  | BoolVar v                  -> Option.map_default (fun x->[x]) [] (var_th v)
  | PC (pc,t,_)                -> Option.map_default (fun x->[x]) [] t
  | PCUpdate (pc,t)            -> [t]
  | PCRange (pc1,pc2,t,_)      -> Option.map_default (fun x->[x]) [] t


and voc_eq ((t1,t2):eq) : tid list = (voc_term t1) @ (voc_term t2)


and voc_ineq ((t1,t2):diseq) : tid list = (voc_term t1) @ (voc_term t2)


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


let all_voc (phi:formula) : ThreadSet.t =
  let th_list = voc_formula phi in
  let th_set  = List.fold_left (fun set e -> ThreadSet.add e set)
                               (ThreadSet.empty)
                               (th_list)
  in
    th_set


let voc (phi:formula) : tid list =
  ThreadSet.elements (all_voc phi)


let conjformula_voc (cf:conjunctive_formula) : tid list =
  let th_list = voc_conjunctive_formula cf in
  let th_set = List.fold_left (fun set e -> ThreadSet.add e set)
                              (ThreadSet.empty)
                              (th_list)
  in
    ThreadSet.elements th_set


let unprimed_voc (phi:formula) : tid list =
  let voc_set = ThreadSet.filter (is_primed_tid>>not) (all_voc phi)
  in
    ThreadSet.elements voc_set

    

(*********)
(* FOLDS *)
(*********)
(* type ('s,'e,'th,'a,'c,'sth,'p,'m,'t) term_maps = { *)
(*     term_var_f : varId -> 't; *)
(*     set_f      : set   -> 's   -> 't; *)
(*     elem_f     : elem  -> 'e   -> 't; *)
(*     tid_f     : tid  -> 'th  -> 't; *)
(*     addr_f     : addr  -> 'a   -> 't; *)
(*     cell_f     : cell  -> 'c   -> 't; *)
(*     setth_f    : setth -> 'sth -> 't; *)
(*     path_f     : path  -> 'p   -> 't; *)
(*     mem_f      : mem   -> 'm   -> 't; *)
(* } *)
    
(* type ('e,'p,'m,'a,'s) set_maps = { *)
(*   set_var_f   : varId  -> 's; *)
(*   empty_f     : 's; *)
(*   singl_f     : addr -> 'e -> 's; *)
(*   union_f     : set * set -> 's -> 's -> 's; *)
(*   intr_f      : set * set -> 's -> 's -> 's; *)
(*   diff_f      : set * set -> 's -> 's -> 's; *)
(*   pathtoset_f : path -> 'p -> 's; *)
(*   addrtoset_f : mem * addr -> 'm -> 'a -> 's; *)
(* } *)


(* type ('c,'th) tid_maps = { *)
(*   tid_var_f   : varId -> 'th ; *)
(*   notid_f     : 'th ; *)
(*   celllockid_f : cell -> 'c -> 'th ; *)
(* } *)

(* type ('c,'e) elem_maps = { *)
(*   elem_var_f   : varId -> 'e; *)
(*   celldata_f   : cell -> 'c -> 'e; *)
(* } *)

(* type ('c,'m,'p,'e,'th,'a) addr_maps = { *)
(*     addr_var_f  : varId -> 'a; *)
(*     null_f      : 'a ; *)
(*     next_f      : cell -> 'c -> 'a ; *)
(*     fstlocked_f : mem * path -> 'm -> 'p -> 'a ; *)
(*     malloc_f    : elem * addr * tid -> 'e -> 'a -> 'th -> 'a ; *)
(* } *)


(* type ('e,'a,'th,'m,'c) cell_maps = { *)
(*   cell_var_f    : varId -> 'c; *)
(*   error_f       : 'c ; *)
(*   mkcell_f      : elem * addr * tid -> 'e -> 'a -> 'th -> 'c ; *)
(*   celllock_f    : cell -> 'c -> 'c ; *)
(*   cellunlock_f  : cell -> 'c -> 'c ; *)
(*   cellat_f      : mem * addr -> 'm -> 'a -> 'c ; *)
(* } *)

(* type ('th,'st) setth_maps = { *)
(*   setth_var_f   : varId  -> 'st; *)
(*   emptyth_f     : 'st ; *)
(*   singlth_f     : tid -> 'th -> 'st ; *)
(*   unionth_f     : setth * setth -> 'st -> 'st -> 'st ; *)
(*   intrth_f      : setth * setth -> 'st -> 'st -> 'st ; *)
(*   diffth_f      : setth * setth -> 'st -> 'st -> 'st ; *)
(* } *)


(* type ('a,'m,'p) path_maps = { *)
(*   path_var_f  : varId -> 'p ; *)
(*   epsilon_f   : 'p ; *)
(*   simple_f    : addr -> 'a -> 'p ; *)
(*   getp_f      : mem * addr * addr -> 'm -> 'a -> 'a -> 'p ; *)
(* } *)

(* type ('a,'c,'m) mem_maps = { *)
(*   mem_var_f     : varId -> 'm; *)
(*   emp_f         : 'm ; *)
(*   update_f      : mem * addr * cell -> 'm -> 'a -> 'c -> 'm; *)
(* } *)


(* type ('p,'m,'a,'s,'th,'st,'t,'l) literal_maps = { *)
(*   append_f    : path * path * path -> 'p -> 'p -> 'p -> 'l; *)
(*   reach_f     : mem * addr * addr * path -> 'm -> 'a -> 'a -> 'p -> 'l; *)
(*   in_f        : addr * set -> 'a -> 's -> 'l; *)
(*   subset_f    : set * set -> 's -> 's -> 'l; *)
(*   inth_f      : tid * setth -> 'th -> 'st -> 'l; *)
(*   subsetth_f  : setth * setth -> 'st -> 'st -> 'l; *)
(*   lit_eq_f    : term * term -> 't -> 't -> 'l; *)
(*   lit_ineq_f  : term * term -> 't -> 't -> 'l; *)
(* } *)

(* type ('f,'l) formula_maps = { *)
(*     form_literal_f  : literal -> 'l -> 'f; *)
(*     true_f    : 'f; *)
(*     false_f   : 'f; *)
(*     and_f     : formula * formula -> 'f -> 'f -> 'f; *)
(*     or_f      : formula * formula -> 'f -> 'f -> 'f; *)
(*     not_f     : formula -> 'f -> 'f; *)
(*     implies_f : formula * formula -> 'f -> 'f -> 'f; *)
(*     iff_f     : formula * formula -> 'f -> 'f -> 'f; *)
(* } *)


(* type  ('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps = { *)
(*     term_m     : ('s,'e,'th,'a,'c,'sth,'p,'m,'t) term_maps; *)
(*     set_m      : ('e,'p,'m,'a,'s) set_maps; *)
(*     tid_m     : ('c,'th) tid_maps; *)
(*     elem_m     : ('c,'e) elem_maps; *)
(*     addr_m     : ('c,'m,'p,'e,'th,'a) addr_maps; *)
(*     cell_m     : ('e,'a,'th,'m,'c) cell_maps; *)
(*     setth_m    : ('th,'sth) setth_maps; *)
(*     path_m     : ('a,'m,'p) path_maps; *)
(*     mem_m      : ('a,'c,'m) mem_maps; *)
(*     literal_m  : ('p,'m,'a,'s,'th,'sth,'t,'l) literal_maps; *)
(*     formula_m  : ('f,'l) formula_maps; *)
(* } *)


(* let fold_term2 (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (t:term) = *)
(*   fs.term_m.term_var_f "" *)


(* let rec fold_term (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (t:term) = *)
(*   match t with *)
(*       VarT v   -> fs.term_m.term_var_f v *)
(*     | SetT s   -> fs.term_m.set_f   s (fold_set   fs s) *)
(*     | ElemT e  -> fs.term_m.elem_f  e (fold_elem  fs e) *)
(*     | ThidT i  -> fs.term_m.tid_f  i (fold_tid  fs i) *)
(*     | AddrT a  -> fs.term_m.addr_f  a (fold_addr  fs a) *)
(*     | CellT c  -> fs.term_m.cell_f  c (fold_cell  fs c) *)
(*     | SetThT s -> fs.term_m.setth_f s (fold_setth fs s) *)
(*     | PathT p  -> fs.term_m.path_f  p (fold_path  fs p) *)
(*     | MemT m   -> fs.term_m.mem_f   m (fold_mem   fs m) *)
(* and fold_set (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (s:set) = *)
(*   match s with *)
(*     VarSet v        -> fs.set_m.set_var_f v *)
(*   | EmptySet        -> fs.set_m.empty_f *)
(*   | Singl a         -> fs.set_m.singl_f a (fold_addr fs a) *)
(*   | Union (s1,s2)   -> fs.set_m.union_f (s1,s2) (fold_set fs s1) (fold_set fs s2) *)
(*   | Intr (s1,s2)    -> fs.set_m.intr_f  (s1,s2) (fold_set fs s1) (fold_set fs s2) *)
(*   | Setdiff (s1,s2) -> fs.set_m.diff_f  (s1,s2) (fold_set fs s1) (fold_set fs s2) *)
(*   | PathToSet (p)   -> fs.set_m.pathtoset_f p (fold_path fs p) *)
(*   | AddrToSet (m,a) -> fs.set_m.addrtoset_f (m,a) (fold_mem fs m) (fold_addr fs a) *)
(* and fold_tid (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (th:tid) = *)
(*   match th with *)
(*     VarTh v        -> fs.tid_m.tid_var_f v *)
(*   | NoThid         -> fs.tid_m.notid_f *)
(*   | CellLockId (c) -> fs.tid_m.celllockid_f c (fold_cell fs c) *)
(* and fold_elem (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (e:elem) = *)
(*   match e with *)
(*     VarElem   v  -> fs.elem_m.elem_var_f v *)
(*   | CellData (c) -> fs.elem_m.celldata_f c (fold_cell fs c) *)
(* and fold_addr (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (a:addr) = *)
(*   match a with *)
(*     VarAddr v -> fs.addr_m.addr_var_f v *)
(*   | Null      -> fs.addr_m.null_f *)
(*   | Next (c)  -> fs.addr_m.next_f c (fold_cell fs c) *)
(*   | FirstLocked (m,p) -> fs.addr_m.fstlocked_f (m,p) (fold_mem fs m)  *)
(*                                                      (fold_path fs p) *)
(*   | Malloc (e,a,t) -> fs.addr_m.malloc_f (e,a,t) (fold_elem fs e) *)
(*                                                  (fold_addr fs a) *)
(*                                          val_tid fs t) *)
(* and fold_cell (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (c:cell) ; *)
(*   match c with *)
(*     VarCell v -> fs.cell_m.cell_var_f v *)
(*   | Error     -> fs.cell_m.error_f *)
(*   | MkCell (e,a,t) -> fs.cell_m.mkcell_f (e,a,t) (fold_elem fs e) *)
(*                                                  (fold_addr fs a) *)
(*                                                  (fold_tid fs t) *)
(*   | CellLock (c) -> fs.cell_m.celllock_f  c (fold_cell fs c) *)
(*   | CellUnlock (c) -> fs.cell_m.cellunlock_f c (fold_cell fs c) *)
(*   | CellAt (m,a) -> fs.cell_m.cellat_f (m,a) (fold_mem fs m) (fold_addr fs a) *)
(* and fold_setth (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (sth:setth) = *)
(*   match sth with *)
(*     VarSetTh v  -> fs.setth_m.setth_var_f v *)
(*   | EmptySetTh  -> fs.setth_m.emptyth_f *)
(*   | SinglTh t   -> fs.setth_m.singlth_f t (fold_tid fs t) *)
(*   | UnionTh (s1,s2) -> fs.setth_m.unionth_f (s1,s2) (fold_setth fs s1)  *)
(*                                                     (fold_setth fs s2) *)
(*   | IntrTh (s1,s2) -> fs.setth_m.intrth_f (s1,s2) (fold_setth fs s1)  *)
(*                                                   (fold_setth fs s2) *)
(*   | SetdiffTh (s1,s2) -> fs.setth_m.diffth_f (s1,s2) (fold_setth fs s1)  *)
(*                                                      (fold_setth fs s2) *)
(* and fold_path (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (p:path) = *)
(*   match p with *)
(*     VarPath v -> fs.path_m.path_var_f v *)
(*   | Epsilon   -> fs.path_m.epsilon_f *)
(*   | SimplePath (a) -> fs.path_m.simple_f a (fold_addr fs a) *)
(*   | GetPath (m,a1,a2) -> fs.path_m.getp_f (m,a1,a2) (fold_mem fs m) *)
(*                                                     (fold_addr fs a1) *)
(*                                                     (fold_addr fs a2) *)
(* and fold_mem (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (m:mem) = *)
(*   match m with *)
(*       VarMem v       -> fs.mem_m.mem_var_f v *)
(*     | Emp            -> fs.mem_m.emp_f *)
(*     | Update (m,a,c) -> fs.mem_m.update_f (m,a,c) (fold_mem fs m)  *)
(*                                            (fold_addr fs a)  *)
(*                                                   (fold_cell fs c) *)
(* and fold_literal (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (l:literal) = *)
(*   match l with *)
(*   | Append (p1,p2,p3) -> fs.literal_m.append_f (p1,p2,p3) (fold_path fs p1) *)
(*                                                           (fold_path fs p2) *)
(*                                                           (fold_path fs p3) *)
(*   | Reach (m,a1,a2,p) -> fs.literal_m.reach_f (m,a1,a2,p) (fold_mem fs m) *)
(*                                                           (fold_addr fs a1) *)
(*                                                           (fold_addr fs a2) *)
(*                                                           (fold_path fs p) *)
(*   | In (a,s) -> fs.literal_m.in_f (a,s) (fold_addr fs a) (fold_set fs s) *)
(*   | SubsetEq (s1,s2) -> fs.literal_m.subset_f (s1,s2) (fold_set fs s1)  *)
(*                                                       (fold_set fs s2) *)
(*   | InTh (t,s) -> fs.literal_m.inth_f (t,s) (fold_tid fs t) (fold_setth fs s) *)
(*   | SubsetEqTh (s1,s2) -> fs.literal_m.subsetth_f (s1,s2) (fold_setth fs s1) *)
(*                                                           (fold_setth fs s2) *)
(*   | Eq   (x,y) -> fs.literal_m.lit_eq_f   (x,y) (fold_term fs x) (fold_term fs y) *)
(*   | InEq (x,y) -> fs.literal_m.lit_ineq_f (x,y) (fold_term fs x) (fold_term fs y) *)
(* and fold_formula (fs:('t,'s,'th,'e,'a,'c,'sth,'p,'m,'l,'f) all_maps) (f:formula) = *)
(*   match f with *)
(*       Literal (l) -> fs.formula_m.form_literal_f l (fold_literal fs l) *)
(*     | True  -> fs.formula_m.true_f *)
(*     | False -> fs.formula_m.false_f *)
(*     | And (f1,f2) -> fs.formula_m.and_f (f1,f2) (fold_formula fs f1) (fold_formula fs f2) *)
(*     | Or (f1,f2)  -> fs.formula_m.or_f  (f1,f2) (fold_formula fs f1) (fold_formula fs f2) *)
(*     | Not (f')    -> fs.formula_m.not_f f' (fold_formula fs f') *)
(*     | Implies (f1,f2) -> fs.formula_m.implies_f  (f1,f2) (fold_formula fs f1)  *)
(*                                                   (fold_formula fs f2) *)
(*     | Iff (f1,f2) -> fs.formula_m.iff_f (f1,f2) (fold_formula fs f1)  *)
(*                                          (fold_formula fs f2) *)
(**************************)
(* converters as folds    *)
(**************************)


(* (\* variable_to_str fold function *\) *)
(* let var_to_str id = id *)

(* (\* array_to_str fold function *\) *)
(* let array_to_str _ arr t = sprintf "%s%s" arr t *)


(* (\* literal_to_str fold functions *\) *)
(* let lit_append_to_str _ p1 p2 pres = sprintf "append(%s,%s,%s)" p1 p2 pres *)
(* let lit_reach_to_str _ h a1 a2 p   = sprintf "reach(%s,%s,%s,%s)" h a1 a2 p *)
(* let lit_in_to_str _ a s            = sprintf "%s in %s" a s *)
(* let lit_subseteq_to_str _ s1 s2    = sprintf "%s subseteq %s" s1 s2 *)
(* let lit_inth_to_str _ t s          = sprintf "%s inTh %s" t s *)
(* let lit_subseteqth_to_str _ s1 s2  = sprintf "%s subseteqTh %s" s1 s2 *)
(* let lit_eq_to_str _ e1 e2 = sprintf "%s = %s" e1 e2 *)
(* let lit_ineq_to_str _ e1 e2 =  sprintf "%s != %s" e1 e2 *)

(* (\* memory_to_str fold functions *\) *)
(* let mem_update_to_str _ m a c    = sprintf "upd(%s,%s,%s)" m a c *)
(* let mem_emp_to_str _ = sprintf "emp" *)

(* (\* path_to_str fold functions *\) *)
(* let path_epsilon_to_str          = "epsilon" *)
(* let path_simple_to_str _ a       = sprintf "[ %s ]" a *)
(* let path_getp_to_str   _ m a1 a2 = sprintf "getp(%s,%s,%s)" m a1 a2 *)

(* (\* set_to_str fold funtion *\) *)
(* let set_empty_to_str             = "EmptySet" *)
(* let set_singl_to_str _ a         = sprintf "{ %s }" a *)
(* let set_union_to_str _ s1 s2     = sprintf "%s Union %s" s1 s2 *)
(* let set_intr_to_str  _ s1 s2     = sprintf "%s Intr %s" s1 s2 *)
(* let set_diff_to_str  _ s1 s2     = sprintf "%s SetDiff %s" s1 s2 *)
(* let set_pathtoset_to_str _ p     = sprintf "path2set(%s)" p *)
(* let set_addrtoset_to_str _ m a   = sprintf "addr2set(%s,%s)" m a *)

(* (\* setth_to_str fold funtion *\) *)
(* let setth_empty_to_str            = "EmptySetTh" *)
(* let setth_singl_to_str _ a        = sprintf "SingleTh(%s)" a *)
(* let setth_union_to_str _ s1 s2    = sprintf "%s UnionTh %s" s1 s2 *)
(* let setth_intr_to_str  _ s1 s2    = sprintf "%s IntrTh %s" s1 s2 *)
(* let setth_diff_to_str  _ s1 s2    = sprintf "%s SetDiffTh %s" s1 s2 *)
(* let setth_addrtoset_to_str _ m a  = sprintf "addr2set(%s,%s)" m a *)

(* (\* cell_to_str fold function *\) *)
(* let cell_error_to_str           = "Error" *)
(* let cell_mkcell_to_str _ d a t  = sprintf "mkcell(%s,%s,%s)" d a t *)
(* let cell_lock_to_str _ c        = sprintf "%s.lock" c *)
(* let cell_unlock_to_str _ c      = sprintf "%s.unlock" c *)
(* let cell_at_to_str _ m a        = sprintf "%s [ %s ]" m a *)

(* (\* addr_to_str fold function *\) *)
(* let addr_null_to_str            = "null" *)
(* let addr_next_to_str      _ c     = sprintf "%s.next" c *)
(* let addr_fstlocked_to_str _ m p   = sprintf "firstlocked(%s,%s)" m p *)
(* let addr_array_to_str     _ arr t = array_to_str arr t *)
(* let addr_malloc_to_str    _ e a t = sprintf "malloc(%s,%s,%s)" e a t *)

(* (\* tid_to_str fold functions *\) *)
(* let tid_notid_to_str          = "#" *)
(* let tid_lockid_to_str _ c      = sprintf "%s.lockid" c *)


(* (\* elem_to_str fold functions *\) *)
(* let elem_celldata_to_str _ c      = sprintf "%s.data" c *)

(* (\* term_to_str fold functions *\) *)
(* let term_set_to_str   _ s  = s *)
(* let term_addr_to_str  _ a  = a *)
(* let term_elem_to_str  _ e  = e *)
(* let term_tid_to_str  _ t  = t *)
(* let term_cell_to_str  _ c  = c *)
(* let term_setth_to_str _ s  = s *)
(* let term_path_to_str  _ p  = p *)
(* let term_mem_to_str   _ m  = m *)


(* (\* formula_to_str fold functions *\) *)

(* let formula_literal_to_str _ l = l *)

(* let formula_true_to_str  = "true" *)
(* let formula_false_to_str = "false" *)
(* let formula_and_to_str     _ f1 f2 = sprintf "%s /\\ %s" f1 f2 *)
(* let formula_or_to_str      _ f1 f2 = sprintf "%s \\/ %s" f1 f2 *)
(* let formula_not_to_str     _ f     = sprintf "~ %s" f *)
(* let formula_implies_to_str _ f1 f2 = sprintf "%s -> %s" f1 f2 *)
(* let formula_iff_to_str     _ f1 f2 = sprintf "%s <-> %s" f1 f2 *)

(* let to_str_maps = { *)
(*   literal_m = { *)
(*     append_f    = lit_append_to_str; *)
(*     reach_f     = lit_reach_to_str; *)
(*     in_f        = lit_in_to_str; *)
(*     subset_f    = lit_subseteq_to_str; *)
(*     inth_f      = lit_inth_to_str; *)
(*     subsetth_f  = lit_subseteqth_to_str; *)
(*     lit_eq_f    = lit_eq_to_str; *)
(*     lit_ineq_f  = lit_ineq_to_str; *)
(*   }; *)

(*   mem_m = { *)
(*     mem_var_f = var_to_str; *)
(*     emp_f     = "emp" ; *)
(*     update_f  = mem_update_to_str; *)
(*   }; *)

(*   path_m = { *)
(*     path_var_f = var_to_str; *)
(*     epsilon_f = path_epsilon_to_str; *)
(*     simple_f = path_simple_to_str; *)
(*     getp_f = path_getp_to_str; *)
(*   }; *)

(*   set_m = { *)
(*     set_var_f = var_to_str; *)
(*     empty_f = set_empty_to_str; *)
(*     singl_f = set_singl_to_str; *)
(*     union_f = set_union_to_str; *)
(*     intr_f = set_intr_to_str; *)
(*     diff_f = set_diff_to_str; *)
(*     pathtoset_f = set_pathtoset_to_str; *)
(*     addrtoset_f = set_addrtoset_to_str; *)
(*   }; *)

(*   setth_m = { *)
(*     setth_var_f = var_to_str; *)
(*     emptyth_f = set_empty_to_str; *)
(*     singlth_f = set_singl_to_str; *)
(*     unionth_f = set_union_to_str; *)
(*     intrth_f = set_intr_to_str; *)
(*     diffth_f = set_diff_to_str; *)
(*   }; *)

(*   cell_m = { *)
(*     cell_var_f = var_to_str; *)
(*     error_f = cell_error_to_str; *)
(*     mkcell_f = cell_mkcell_to_str; *)
(*     celllock_f = cell_lock_to_str; *)
(*     cellunlock_f = cell_unlock_to_str; *)
(*     cellat_f = cell_at_to_str; *)
(*   }; *)

(*   addr_m = { *)
(*     addr_var_f = var_to_str; *)
(*     null_f = addr_null_to_str; *)
(*     next_f = addr_next_to_str; *)
(*     fstlocked_f = addr_fstlocked_to_str; *)
(*     malloc_f = addr_malloc_to_str; *)
(*   }; *)

(*   tid_m = { *)
(*     tid_var_f = var_to_str; *)
(*     notid_f = tid_notid_to_str; *)
(*     celllockid_f = tid_lockid_to_str; *)
(*   }; *)

(*   elem_m = { *)
(*     elem_var_f = var_to_str; *)
(*     celldata_f = elem_celldata_to_str; *)
(*   }; *)

(*   term_m = { *)
(*     term_var_f = var_to_str; *)
(*     set_f = term_set_to_str; *)
(*     elem_f = term_elem_to_str; *)
(*     tid_f = term_tid_to_str; *)
(*     addr_f = term_addr_to_str; *)
(*     cell_f = term_cell_to_str; *)
(*     setth_f = term_setth_to_str; *)
(*     path_f = term_path_to_str; *)
(*     mem_f = term_mem_to_str; *)
(*   }; *)

(*   formula_m = { *)
(*     form_literal_f = formula_literal_to_str; *)
(*     true_f = formula_true_to_str; *)
(*     false_f = formula_false_to_str; *)
(*     and_f = formula_and_to_str; *)
(*     or_f = formula_or_to_str; *)
(*     not_f = formula_not_to_str; *)
(*     implies_f = formula_implies_to_str; *)
(*     iff_f = formula_iff_to_str; *)
(*   }; *)

(* } *)


(* let literal_to_str l   = fold_literal to_str_maps l *)
(* let mem_to_str m       = fold_mem     to_str_maps m *)
(* let path_to_str p      = fold_path    to_str_maps p *)
(* let set_to_str s       = fold_set     to_str_maps s *)
(* let cell_to_str c      = fold_cell    to_str_maps c *)
(* let addr_to_str a      = fold_addr    to_str_maps a *)
(* let tid_to_str th     = fold_tid    to_str_maps th *)
(* let setth_to_str sth   = fold_setth   to_str_maps sth *)
(* let elem_to_str e      = fold_elem    to_str_maps e *)
(* let term_to_str t      = fold_term    to_str_maps t *)
(* let formula_to_str phi = fold_formula to_str_maps phi *)



(* let conjunctive_formula_to_str form = *)
(*   let rec c_to_str f str = *)
(*     match f with *)
(*  [] -> str *)
(*       | lit::sub ->  *)
(*    c_to_str sub (Printf.sprintf "%s /\\ %s" str (literal_to_str lit)) *)
(*   in *)
(*     match form with *)
(*  [] -> "" *)
(*       | lit :: subform -> c_to_str subform (literal_to_str lit) *)


(******************************)
(* DNF                        *)
(******************************)

let rec nnf expr =
  match expr with
      False -> False
    | True  -> True
    | Iff (e1,e2)    -> And (nnf (Implies (e1,e2)),nnf (Implies(e2,e1)))
    | Implies(e1,e2) -> Or (nnf (Not e1), nnf e2)
    | And(e1,e2)     -> And(nnf e1, nnf e2)
    | Or(e1,e2)      -> Or(nnf e1, nnf e2)
    | Not (Not e)    -> nnf e
    | Not (And (e1,e2)) -> Or (nnf (Not e1), nnf (Not e2))
    | Not (Or (e1, e2)) -> And (nnf (Not e1), nnf (Not e2))
    | Not (Implies (e1, e2)) ->And (nnf e1, nnf (Not e2))
    | Not (Iff (e1, e2)) ->  Or (And (nnf e1, nnf (Not e2)), And (nnf (Not e1), nnf e2))
    | Not Literal(Atom a) -> Literal(NegAtom a)
    | Not Literal(NegAtom a) -> Literal(Atom a)
    | Not True  -> False
    | Not False -> True
    | Literal(a) -> Literal(a)
      
exception ErrorInNNF of string


let rec dnf (expr:formula) : conjunctive_formula list =
  let rec dnf_nnf nnfexpr =
    match nnfexpr with
      Or(e1,e2)  ->
        begin
          match (dnf_nnf e1, dnf_nnf e2) with
            ([TrueConj],_)  -> [TrueConj]
          | (_,[TrueConj])  -> [TrueConj]
          | ([FalseConj],x) -> x
          | (x,[FalseConj]) -> x
          | (lx,ly) -> lx @ ly
        end
    | And(e1,e2) ->
        begin
          match (dnf_nnf e1, dnf_nnf e2) with
            ([FalseConj],_) -> [FalseConj]
          | (_,[FalseConj]) -> [FalseConj]
          | ([TrueConj],x)  -> x
          | (x,[TrueConj])  -> x
          | (e1_dnf, e2_dnf) ->
                let get_conjuncts c =
                  match c with
                    Conj l -> l
                  | _ -> let msg = "Formula "^(formula_to_str nnfexpr)^" is not in NNF.\n" in
                           raise(ErrorInNNF(msg))
                in
                (* here lx and ly  are lists of Conj none of which is 
                 * True or False *)
                let add_to_all_in_e2 final_list x1 =
                  let lx1 = get_conjuncts x1 in
                  let add_x1 l2 x2 = Conj(lx1 @ (get_conjuncts x2))::l2 in
                  let lst = List.fold_left add_x1 [] e2_dnf in
                    lst @ final_list
                in
                  List.fold_left add_to_all_in_e2 [] e1_dnf
        end
    | Literal(l) -> [ Conj [ l ]]
    | True       -> [TrueConj]
    | False      -> [FalseConj]
    | _          -> let msg = "Formula " ^(formula_to_str nnfexpr)^ " is not in NNF.\n" in
                      raise(ErrorInNNF(msg))
  in
    dnf_nnf (nnf expr)


let rec split_conj (phi:formula) : formula list =
  match phi with
    And (phi1, phi2) -> (split_conj phi1) @ (split_conj phi2)
  | _                -> [phi]


let required_sorts (phi:formula) : sort list =
  let empty = SortSet.empty in
  let union = SortSet.union in
  let add = SortSet.add in
  let single = SortSet.singleton in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in

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

  and req_atom (a:atom) : SortSet.t =
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
    | VarCell _         -> single Cell
    | Error             -> single Cell
    | MkCell (e,a,t)    -> append Cell [req_e e;req_a a; req_t t]
    | CellLock (c,t)    -> append Cell [req_c c;req_t t]
    | CellUnlock c      -> append Cell [req_c c]
    | CellAt (m,a)      -> append Cell [req_m m;req_a a]

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _         -> single Addr
    | Null              -> single Addr
    | Next c            -> append Addr [req_c c]
    | FirstLocked (m,p) -> append Addr [req_m m;req_p p]

  and req_e (e:elem) : SortSet.t =
    match e with
    | VarElem _         -> single Elem
    | CellData c        -> append Elem [req_c c]
    | HavocListElem     -> single Elem
    | LowestElem        -> single Elem
    | HighestElem       -> single Elem

  and req_t (t:tid) : SortSet.t =
    match t with
    | VarTh _           -> single Thid
    | NoThid            -> single Thid
    | CellLockId c      -> append Thid [req_c c]

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
    | VarT (_,s,_,_,_)             -> single s
    | SetT s                       -> req_s s
    | ElemT e                      -> req_e e
    | ThidT t                      -> req_t t
    | AddrT a                      -> req_a a
    | CellT c                      -> req_c c
    | SetThT s                     -> req_st s
    | SetElemT s                   -> req_se s
    | PathT p                      -> req_p p
    | MemT m                       -> req_m m
    | VarUpdate ((_,s,_,_,_),t,tr) -> append s [req_t t;req_term tr]
  in
    SortSet.elements (req_f phi)

 

let special_ops (phi:formula) : special_op_t list =
  let empty = OpsSet.empty in
  let union = OpsSet.union in
  let add = OpsSet.add in
  let list_union xs = List.fold_left union empty xs in
  let append s sets = add s (List.fold_left union empty sets) in

  let rec ops_f (phi:formula) : OpsSet.t =
    match phi with
    | Literal l       -> ops_l l
    | True            -> empty
    | False           -> empty
    | And (f1,f2)     -> union (ops_f f1) (ops_f f2)
    | Or (f1,f2)      -> union (ops_f f1) (ops_f f2)
    | Not f           -> ops_f f
    | Implies (f1,f2) -> union (ops_f f1) (ops_f f2)
    | Iff (f1,f2)     -> union (ops_f f1) (ops_f f2)

  and ops_l (l:literal) : OpsSet.t =
    match l with
    | Atom a    -> ops_atom a
    | NegAtom a -> ops_atom a

  and ops_atom (a:atom) : OpsSet.t =
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
    | LessElem (e1,e2)    -> append ElemOrder [ops_e e1; ops_e e2]
    | GreaterElem (e1,e2) -> append ElemOrder [ops_e e1; ops_e e2]
    | Eq (t1,t2)          -> list_union [ops_term t1;ops_term t2]
    | InEq (t1,t2)        -> list_union [ops_term t1;ops_term t2]
    | BoolVar v           -> empty
    | PC _                -> empty
    | PCUpdate _          -> empty
    | PCRange _           -> empty

  and ops_m (m:mem) : OpsSet.t =
    match m with
    | VarMem _         -> empty
    | Emp              -> empty
    | Update (m,a,c)   -> list_union [ops_m m;ops_a a;ops_c c]

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
    | VarCell _         -> empty
    | Error             -> empty
    | MkCell (e,a,t)    -> list_union [ops_e e;ops_a a; ops_t t]
    | CellLock (c,t)    -> list_union [ops_c c;ops_t t]
    | CellUnlock c      -> list_union [ops_c c]
    | CellAt (m,a)      -> list_union [ops_m m;ops_a a]

  and ops_a (a:addr) : OpsSet.t =
    match a with
    | VarAddr _         -> empty
    | Null              -> empty
    | Next c            -> list_union [ops_c c]
    | FirstLocked (m,p) -> append FstLocked [ops_m m;ops_p p]

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
    | NoThid            -> empty
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
    | ThidT t            -> ops_t t
    | AddrT a            -> ops_a a
    | CellT c            -> ops_c c
    | SetThT s           -> ops_st s
    | SetElemT s         -> ops_se s
    | PathT p            -> ops_p p
    | MemT m             -> ops_m m
    | VarUpdate (_,t,tr) -> list_union [ops_t t;ops_term tr]
  in
    OpsSet.elements (ops_f phi)



let cleanup_dup (cf:conjunctive_formula) : conjunctive_formula =
  let clean_lits (ls:literal list) : literal list =
    let (_, xs) = List.fold_left (fun (s,xs) l ->
                    if LiteralSet.mem l s then
                      (s,xs)
                    else
                      (LiteralSet.add l s, l::xs)
                  ) (LiteralSet.empty, []) ls
    in
      List.rev xs
  in
    match cf with
    | TrueConj -> TrueConj
    | FalseConj -> FalseConj
    | Conj ls -> Conj (clean_lits ls)


(* NOTE: I am not considering the possibility of having a1=a2 \/ a1=a3 in the formula *)
let rec get_addrs_eqs (phi:formula) : ((addr*addr) list * (addr*addr) list) =
  match phi with
  | Literal l   -> get_addrs_eqs_lit l
  | And (f1,f2) -> let (es1,is1) = get_addrs_eqs f1 in
                   let (es2,is2) = get_addrs_eqs f2 in
                     (es1@es2, is1@is2)
  | Not f       -> let (es,is) = get_addrs_eqs f in (is,es)
  | _           -> ([],[])

and get_addrs_eqs_conj (cf:conjunctive_formula) : ((addr*addr) list * (addr*addr) list) =
  match cf with
  | TrueConj -> ([],[])
  | FalseConj -> ([],[])
  | Conj xs -> List.fold_left (fun (es,is) l ->
                 let (es',is') = get_addrs_eqs_lit l in
                 (es@es', is@is')
               ) ([],[]) xs

and get_addrs_eqs_lit (l:literal) : ((addr*addr) list * (addr*addr) list) =
  match l with
  | Atom a -> get_addrs_eqs_atom a
  | NegAtom a -> let (es,is) = get_addrs_eqs_atom a in (is,es)

and get_addrs_eqs_atom (a:atom) : ((addr*addr) list * (addr*addr) list) =
  match a with
  | Eq (AddrT a1, AddrT a2)   -> ([(a1,a2)],[])
  | InEq (AddrT a1, AddrT a2) -> ([],[(a1,a2)])
  | _ -> ([],[])
  
