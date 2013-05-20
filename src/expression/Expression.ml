open Printf
open LeapLib
open LeapVerbose


type varId = string

type kind_t = Normal | Ghost

type scope_t = Global | Local

type pc_t = int

and initVal_t = Equality of term | Condition of formula

and var_info_t = sort * initVal_t option * tid option * kind_t

and sort =
    Set
  | Elem
  | Thid
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


and variable = varId * sort * bool * tid option * string option * kind_t


and term =
    VarT          of variable
  | SetT          of set
  | ElemT         of elem
  | ThidT         of tid
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
    VarArray      of variable
  | ArrayUp       of arrays * tid * expr_t

and addrarr =
  | VarAddrArray  of variable
  | AddrArrayUp   of addrarr * integer * addr
  | CellArr       of cell

and tidarr =
  | VarTidArray   of variable
  | TidArrayUp    of tidarr * integer * tid
  | CellTids      of cell

and integer =
    IntVal        of int
  | VarInt        of variable
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
    VarSet        of variable
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
    VarTh         of variable
  | NoThid
  | CellLockId    of cell
  | CellLockIdAt  of cell * integer
  | ThidArrayRd   of arrays * tid
  | ThidArrRd     of tidarr * integer

and elem =
    VarElem           of variable
  | CellData          of cell
  | ElemArrayRd       of arrays * tid
  | HavocListElem
  | HavocSkiplistElem
  | LowestElem
  | HighestElem

and addr =
    VarAddr       of variable
  | Null
  | Next          of cell
  | NextAt        of cell * integer
  | FirstLocked   of mem * path
  | FirstLockedAt of mem * path * integer
  | AddrArrayRd   of arrays * tid
  | AddrArrRd     of addrarr * integer

and cell =
    VarCell       of variable
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

and setth =
    VarSetTh      of variable
  | EmptySetTh
  | SinglTh       of tid
  | UnionTh       of setth * setth
  | IntrTh        of setth * setth
  | SetdiffTh     of setth * setth
  | SetThArrayRd  of arrays * tid

and setint =
    VarSetInt     of variable
  | EmptySetInt
  | SinglInt      of integer
  | UnionInt      of setint * setint
  | IntrInt       of setint * setint
  | SetdiffInt    of setint * setint
  | SetIntArrayRd of arrays * tid

and setelem =
    VarSetElem     of variable
  | EmptySetElem
  | SinglElem      of elem
  | UnionElem      of setelem * setelem
  | IntrElem       of setelem * setelem
  | SetdiffElem    of setelem * setelem
  | SetToElems     of set * mem
  | SetElemArrayRd of arrays * tid

and path =
    VarPath       of variable
  | Epsilon
  | SimplePath    of addr
  | GetPath       of mem * addr * addr
  | GetPathAt     of mem * addr * addr * integer
  | PathArrayRd   of arrays * tid

and mem =
    VarMem        of variable
  | Update        of mem * addr * cell
  | MemArrayRd    of arrays * tid

and atom =
    Append        of path * path * path
  | Reach         of mem * addr * addr * path
  | ReachAt       of mem * addr * addr * integer * path
  | OrderList     of mem * addr * addr
  | Skiplist      of mem * set * integer * addr * addr
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
  | BoolVar       of variable
  | BoolArrayRd   of arrays * tid
  | PC            of pc_t * tid option * bool
  | PCUpdate      of pc_t * tid
  | PCRange       of pc_t * pc_t * tid option * bool

and literal =
    Atom          of atom
  | NegAtom       of atom

and conjunctive_formula =
    FalseConj
  | TrueConj
  | Conj          of literal list

and formula =
    Literal       of literal
  | True
  | False
  | And           of formula * formula
  | Or            of formula * formula
  | Not           of formula
  | Implies       of formula * formula
  | Iff           of formula * formula

and expr_t =
    Term          of term
  | Formula       of formula

and tid_subst_t = (tid * tid) list


type formula_info_t =
  {
    mutable formula : formula    ;
    mutable primed : formula     ;
            voc : tid list       ;
            vars : variable list ;
  }

(* Pool type for tagging expression, formulas, etc. *)

module type PoolType =
  sig
    type t
    val compare : t -> t -> int
  end

module type P =
  sig
    type elt
    type t
    val empty : t
    val tag   : t -> elt -> int
  end

module Pool(PType: PoolType)  =
  struct
    type elt = PType.t
    type t = (elt, int) Hashtbl.t

    let empty : t =
      Hashtbl.create 30

    let tag (p:t) (e:elt) : int =
      if Hashtbl.mem p e then
        Hashtbl.find p e
      else
        let c = Hashtbl.length p in
        let _ = Hashtbl.add p e c in
          c
  end

(* Pool type for tagging expression, formulas, etc. *)

(* Pool of terms *)

module TermPool = Pool(
  struct
    let compare = Pervasives.compare
    type t = term
  end
)
(* Pool of terms *)


module ThreadSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = tid
  end )


let var_compare (x:variable) (y:variable) : int =
  let cmp_p p1 p2 = (p1 = None && (p2 = None || p2 = Some"")) ||
                    (p2 = None && (p1 = None || p1 = Some"")) in
  (* I am not comparing whether ghost/normal kind matches *)
  let (x_id, x_s, x_pr, x_th, x_p, x_k) = x in
  let (y_id, y_s, y_pr, y_th, y_p, y_k) = y in
  let cmp = Pervasives.compare (x_id,x_pr,x_th) (y_id,y_pr,y_th)
  in
    if cmp = 0 then
      if cmp_p x_p y_p then
        0
      else
        Pervasives.compare x_p y_p
    else
      cmp
      

let same_var (x:variable) (y:variable) : bool = 
  (var_compare x y) = 0

module VarSet = Set.Make(
  struct
    let compare = var_compare
    type t = variable
  end )


module VarIdSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = varId
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
exception No_numeric_variable of varId * sort
exception No_variable_term of term
exception Impossible_to_convert of tid
exception Incompatible_assignment of term * expr_t
exception Not_implemented of string




(* Configuration *)
let pc_name             = "pc"
let fresh_set_name      = "$set"
let fresh_elem_name     = "$elem"
let fresh_tid_name      = "$tid"
let fresh_addr_name     = "$addr"
let fresh_cell_name     = "$cell"
let fresh_setth_name    = "$setth"
let fresh_setint_name   = "$setint"
let fresh_setelem_name  = "$setelem"
let fresh_path_name     = "$path"
let fresh_mem_name      = "$mem"
let fresh_bool_name     = "$bool"
let fresh_int_name      = "$int"
let fresh_array_name    = "$array"
let fresh_addrarr_name  = "$addrarr"
let fresh_tidarr_name   = "$tidarr"
let fresh_unknown_name  = "$unknown"


let notid_name      = "NoThread"
let defCountAbsVar  = "N"

let def_var     : variable = (defCountAbsVar, Int, false, None, None, Normal)
let defCountVar : integer  = VarInt def_var



(* The heap *)
let heap     = VarMem ("heap", Mem, false, None, None, Normal)
let aux_heap = VarMem (fresh_mem_name, Mem, false, None, None, Normal)


(* Fresh auxiliary variables *)
let fresh_cell = VarCell (fresh_cell_name, Cell, false, None, None, Normal)


(* PROGRAM POSITION FUNCTIONS *)
let build_pc_range (i:pc_t) (j:pc_t) : pc_t list =
  LeapLib.rangeList i j




(* VARIABLE FUNCTIONS *)
let build_var (id:varId)
              (s:sort)
              (pr:bool)
              (th:tid option)
              (p:string option)
              (k:kind_t) : variable =
  (id, s, pr, th, p, k)


let var_clear_param_info (v:variable) : variable =
  let (id,s,pr,_,p,k) = v
  in
    build_var id s pr None p k


let is_owned_var (v:variable) : bool =
  let (_,_,_,_,p,_) = v
  in
    match p with
      Some proc -> proc <> ""
    | None      -> false


let is_local_var (v:variable) : bool =
  let (_,_,_,_,p,_) = v
  in
    (p <> None && p <> Some "")


let is_global_var (v:variable) : bool =
  not (is_local_var v)


let build_num_tid (i:int) : tid =
  VarTh (build_var ("k" ^ string_of_int i) Thid false None None Normal)


let build_var_tid (id:varId) : tid =
  VarTh (build_var id Thid false None None Normal)


let inject_var_sort (v:variable) (s:sort) : variable =
  let (id,_,pr,th,p,k) = v
  in
    (build_var id s pr th p k)


let var_id (v:variable) : varId =
  let (id,_,_,_,_,_) = v in id


let var_sort (v:variable) : sort =
  let (_,s,_,_,_,_) = v in s


let var_pr (v:variable) : bool =
  let (_,_,pr,_,_,_) = v in pr


let var_th (v:variable) : tid option =
  let (_,_,_,th,_,_) = v in th


let var_proc (v:variable) : string option =
  let (_,_,_,_,p,_) = v in p


let var_k (v:variable) : kind_t =
  let (_,_,_,_,_,k) = v in k


let var_val (v:variable) : int =
  int_of_string (var_id v)

let var_full_info (v:variable) : (varId * sort * bool *
                                  tid option * string option * kind_t) =
  v


let set_var_id (v:variable) (id:varId) : variable =
  let (_,s,pr,th,p,k) = v in (id,s,pr,th,p,k)

let set_var_pr (v:variable) (pr:bool) : variable =
  let (id,s,_,th,p,k) = v in (id,s,pr,th,p,k)

let set_var_th (v:variable) (th:tid option) : variable =
  let (id,s,pr,_,p,k) = v in (id,s,pr,th,p,k)


let var_to_term (v:variable) : term =
  match var_sort v with
    Unknown   -> VarT       v
  | Set       -> SetT       (VarSet        v)
  | Elem      -> ElemT      (VarElem       v)
  | Thid      -> ThidT      (VarTh         v)
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


  | Bool    -> VarT    v



let term_to_var (t:term) : variable =
  match t with
    VarT v -> v
  | SetT  (VarSet v)   -> inject_var_sort v Set
  | ElemT (VarElem v)  -> inject_var_sort v Elem
  | ThidT (VarTh v)    -> inject_var_sort v Thid
  | AddrT (VarAddr v)  -> inject_var_sort v Addr
  | CellT (VarCell v)  -> inject_var_sort v Cell
  | SetThT(VarSetTh v) -> inject_var_sort v SetTh
  | PathT (VarPath v)  -> inject_var_sort v Path
  | MemT  (VarMem v)   -> inject_var_sort v Mem
  | IntT  (VarInt v)   -> inject_var_sort v Int
  | ArrayT(VarArray v) -> inject_var_sort v Array
  | _                  -> RAISE(No_variable_term t)



let term_sort (t:term) : sort =
  match t with
    VarT v       -> var_sort v
  | SetT _       -> Set
  | ElemT _      -> Elem
  | ThidT _      -> Thid
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




(* Equality constructor functions for formulas *)
let eq_set (s1:set) (s2:set) : formula =
  Literal (Atom (Eq (SetT s1, SetT s2)))

let eq_elem (e1:elem) (e2:elem) : formula =
  Literal (Atom (Eq (ElemT e1, ElemT e2)))

let eq_tid (t1:tid) (t2:tid) : formula =
  Literal (Atom (Eq (ThidT t1, ThidT t2)))

let eq_addr (a1:addr) (a2:addr) : formula =
  Literal (Atom (Eq (AddrT a1, AddrT a2)))

let eq_cell (c1:cell) (c2:cell) : formula =
  Literal (Atom (Eq (CellT c1, CellT c2)))

let eq_setth (s1:setth) (s2:setth) : formula =
  Literal (Atom (Eq (SetThT s1, SetThT s2)))

let eq_setint (s1:setint) (s2:setint) : formula =
  Literal (Atom (Eq (SetIntT s1, SetIntT s2)))

let eq_setelem (s1:setelem) (s2:setelem) : formula =
  Literal (Atom (Eq (SetElemT s1, SetElemT s2)))

let eq_path (p1:path) (p2:path) : formula =
  Literal (Atom (Eq (PathT p1, PathT p2)))

let eq_int (i1:integer) (i2:integer) : formula =
  Literal (Atom (Eq (IntT i1, IntT i2)))

let eq_mem (m1:mem) (m2:mem) : formula =
  Literal (Atom (Eq (MemT m1, MemT m2)))

let eq_array (a1:arrays) (a2:arrays) : formula =
  Literal (Atom (Eq (ArrayT a1, ArrayT a2)))

let eq_term (t1:term) (t2:term) : formula =
  Literal (Atom (Eq (t1, t2)))

let eq_tid (t1:tid) (t2:tid) : formula =
  Literal (Atom (Eq (ThidT t1, ThidT t2)))

let ineq_addr (a1:addr) (a2:addr) : formula =
  Literal (Atom (InEq (AddrT a1, AddrT a2)))

let ineq_elem (e1:elem) (e2:elem) : formula =
  Literal (Atom (InEq (ElemT e1, ElemT e2)))

let ineq_tid (t1:tid) (t2:tid) : formula =
  Literal (Atom (InEq (ThidT t1, ThidT t2)))

let atom_form (a:atom) : formula =
  Literal (Atom a)

let pc_form (pc:pc_t) (th:tid option) (pr:bool) : formula =
  Literal (Atom (PC (pc,th,pr)))

let pcupd_form (pc:pc_t) (th:tid) : formula =
  Literal (Atom (PCUpdate (pc,th)))

let less_form (i1:integer) (i2:integer) : formula =
  Literal (Atom (Less (i1, i2)))

let lesseq_form (i1:integer) (i2:integer) : formula =
  Literal (Atom (LessEq (i1, i2)))

let greater_form (i1:integer) (i2:integer) : formula =
  Literal (Atom (Greater (i1, i2)))

let greatereq_form (i1:integer) (i2:integer) : formula =
  Literal (Atom (GreaterEq (i1, i2)))

let subset_form (s1:set) (s2:set) : formula =
  Literal (Atom (SubsetEq (s1, s2)))

let subsetth_form (s1:setth) (s2:setth) : formula =
  Literal (Atom (SubsetEqTh (s1, s2)))

let subsetint_form (s1:setint) (s2:setint) : formula =
  Literal (Atom (SubsetEqInt (s1, s2)))

let in_form (a:addr) (s:set) : formula =
  Literal (Atom (In (a, s)))

let inth_form (t:tid) (s:setth) : formula =
  Literal (Atom (InTh (t, s)))

let inint_form (i:integer) (s:setint) : formula =
  Literal (Atom (InInt (i, s)))

let boolvar (v:variable) : formula =
  Literal (Atom (BoolVar v))


(* Operation constructor functions *)
let exp_in (a:addr) (s:set) : formula =
  Literal (Atom (In (a,s)))

let exp_subset (s1:set) (s2:set) : formula =
  Literal (Atom (SubsetEq (s1,s2)))

let exp_inth (t:tid) (s:setth) : formula =
  Literal (Atom (InTh (t,s)))

let exp_subsetth (s1:setth) (s2:setth) : formula =
  Literal (Atom (SubsetEqTh (s1,s2)))

let exp_inint (i:integer) (s:setint) : formula =
  Literal (Atom (InInt (i,s)))

let exp_subsetint (s1:setint) (s2:setint) : formula =
  Literal (Atom (SubsetEqInt (s1,s2)))

let exp_less (i1:integer) (i2:integer) : formula =
  Literal (Atom (Less (i1,i2)))

let exp_greater (i1:integer) (i2:integer) : formula =
  Literal (Atom (Greater (i1,i2)))

let exp_lesseq (i1:integer) (i2:integer) : formula =
  Literal (Atom (LessEq (i1,i2)))

let exp_greatereq (i1:integer) (i2:integer) : formula =
  Literal (Atom (GreaterEq (i1,i2)))



(* TERMSET MANIPULATION FUNCTIONS *)
let construct_varid_set (xs:varId list) : VarIdSet.t =
  List.fold_left (fun s t -> VarIdSet.add t s) (VarIdSet.empty) xs


let construct_var_set (xs:variable list) : VarSet.t =
  List.fold_left (fun s t -> VarSet.add t s) (VarSet.empty) xs


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
                        let new_terms=[ThidT(CellLockId c); ElemT(CellData c)] 
                        in
                        let new_elems = construct_term_set new_terms in
                          TermSet.union set' new_elems
                      end
                    else
                      s
                | ThidT(CellLockId c) ->
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
                              [AddrT(Next c); ThidT(CellLockId c)] in
                        let new_elems = construct_term_set new_terms in
                          TermSet.union set' new_elems
                      end
                    else
                      s
                | _ -> TermSet.remove t s
  in
    List.fold_left aux t_set t_list




(* LOCALIZATION FUNCTIONS *)

let localize_var_id (v:varId) (p_name:string) : varId =
  sprintf "%s::%s" p_name v


let loc_var_option (v:varId) (p_name:string option) : varId =
  match p_name with
    None    -> v
  | Some "" -> v
  | Some p  -> localize_var_id v p



(* PRIMING FUNCTIONS *)


(* Priming functions used for thread identifiers *)

let prime_var_name (v:varId) : varId =
  v ^ "'"


let is_primed (var:variable) : bool =
  let (_,_,pr,_,_,_) = var in pr


let rec is_primed_array (a:arrays) : bool =
  match a with
    VarArray v       -> is_primed v
  | ArrayUp (a',_,_) -> is_primed_array a'

let rec is_primed_addrarray (a:addrarr) : bool =
  match a with
    VarAddrArray v       -> is_primed v
  | AddrArrayUp (a',_,_) -> is_primed_addrarray a'
  | CellArr c            -> false

let rec is_primed_tidarray (a:tidarr) : bool =
  match a with
    VarTidArray v       -> is_primed v
  | TidArrayUp (a',_,_) -> is_primed_tidarray a'
  | CellTids c            -> false

let is_primed_tid (th:tid) : bool =
  match th with
    VarTh v           -> is_primed v
  | NoThid            -> false
  | CellLockId _      -> false
  | CellLockIdAt _    -> false
  | ThidArrayRd (a,_) -> is_primed_array a
  | ThidArrRd (a,_)   -> is_primed_tidarray a
  (* FIX: Propagate the query inside cell??? *)


let prime_variable (var:variable) : variable =
  let (id,s,_,th,p,k) = var
  in
    build_var id s true th p k


let unprime_variable (var:variable) : variable =
  let (id,s,_,th,p,k) = var
  in
    build_var id s false th p k


let var_base_info = var_clear_param_info>>unprime_variable


(* Priming functions used for thread identifiers *)

let rec priming_option_tid (pr:bool)
                           (prime_set:VarSet.t option)
                           (expr:tid option) : tid option =
  (* This statement primes the thread parameter of expressions *)
  (* Option.lift (priming_th_t pr) expr *)
  (* This statement leaves the thread parameter unprimed *)
  expr


let priming_variable (pr:bool)
                     (prime_set:VarSet.t option)
                     (v:variable) : variable =
  let (id,s,_,th,p,k) = v in
  let v' = build_var id s pr (priming_option_tid pr prime_set th) p k
  in
    match prime_set with
      None   -> v'
(* DO NOT ERASE: This may be needed!!!! *)
    | Some s -> if (VarSet.mem (set_var_th v None) s ||
                    VarSet.mem (v) s                  ) then v' else v
(*      | Some s -> if VarSet.mem v s then v' else v *)


let rec priming_term (pr:bool)
                     (prime_set:VarSet.t option)
                     (expr:term) : term =
  match expr with
    VarT v            -> VarT       (priming_variable   pr prime_set v)
  | SetT(set)         -> SetT       (priming_set        pr prime_set set)
  | AddrT(addr)       -> AddrT      (priming_addr       pr prime_set addr)
  | ElemT(elem)       -> ElemT      (priming_elem       pr prime_set elem)
  | ThidT(th)         -> ThidT      (priming_tid        pr prime_set th)
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


and priming_expr (pr:bool) (prime_set:VarSet.t option) (expr:expr_t) : expr_t =
  match expr with
    Term t    -> Term (priming_term pr prime_set t)
  | Formula b -> Formula (priming_formula pr prime_set b)


and priming_array (pr:bool) (prime_set:VarSet.t option) (expr:arrays) : arrays =
  match expr with
    VarArray v       -> VarArray (priming_variable pr prime_set v)
  | ArrayUp(arr,t,e) -> ArrayUp  (priming_array pr prime_set arr,
                                  priming_tid   pr prime_set t,
                                  priming_expr  pr prime_set e)

and priming_addrarray (pr:bool) (prime_set:VarSet.t option) (expr:addrarr)
      : addrarr =
  match expr with
    VarAddrArray v       -> VarAddrArray (priming_variable pr prime_set v)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp  (priming_addrarray pr prime_set arr,
                                          priming_int   pr prime_set i,
                                          priming_addr  pr prime_set a)
  | CellArr c            -> CellArr (priming_cell pr prime_set c)

and priming_tidarray (pr:bool) (prime_set:VarSet.t option) (expr:tidarr)
      : tidarr =
  match expr with
    VarTidArray v       -> VarTidArray (priming_variable pr prime_set v)
  | TidArrayUp(arr,i,t) -> TidArrayUp  (priming_tidarray pr prime_set arr,
                                          priming_int  pr prime_set i,
                                          priming_tid  pr prime_set t)
  | CellTids c            -> CellTids (priming_cell pr prime_set c)

and priming_set (pr:bool) (prime_set:VarSet.t option) (e:set) : set =
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


and priming_addr (pr:bool) (prime_set:VarSet.t option) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr (priming_variable pr prime_set v)
  | Null                      -> Null
  | Next(cell)                -> Next(priming_cell pr prime_set cell)
  | NextAt(cell,l)            -> NextAt(priming_cell pr prime_set cell,
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

and priming_elem (pr:bool) (prime_set:VarSet.t option) (e:elem) : elem =
  match e with
    VarElem v          -> VarElem (priming_variable pr prime_set v)
  | CellData(cell)     -> CellData(priming_cell pr prime_set cell)
  | ElemArrayRd(arr,t) -> ElemArrayRd(priming_array pr prime_set arr,
                                      priming_tid pr prime_set t)

  | HavocListElem      -> HavocListElem
  | HavocSkiplistElem  -> HavocSkiplistElem
  | LowestElem         -> LowestElem
  | HighestElem        -> HighestElem


and priming_tid (pr:bool) (prime_set:VarSet.t option) (th:tid) : tid =
  match th with
    VarTh v              -> VarTh (priming_variable pr prime_set v)
  | NoThid               -> NoThid
  | CellLockId(cell)     -> CellLockId(priming_cell pr prime_set cell)
  | CellLockIdAt(cell,l) -> CellLockIdAt(priming_cell pr prime_set cell,
                                         priming_int pr prime_set l)
  | ThidArrayRd(arr,t)   -> ThidArrayRd(priming_array pr prime_set arr,
                                      priming_tid pr prime_set t)
  | ThidArrRd(arr,l)     -> ThidArrRd(priming_tidarray pr prime_set arr,
                                      priming_int pr prime_set l)


and priming_cell (pr:bool) (prime_set:VarSet.t option) (c:cell) : cell =
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


and priming_setth (pr:bool) (prime_set:VarSet.t option) (s:setth) : setth =
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


and priming_setint (pr:bool) (prime_set:VarSet.t option) (s:setint) : setint =
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


and priming_setelem (pr:bool) (prime_set:VarSet.t option) (s:setelem) : setelem =
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

and priming_path (pr:bool) (prime_set:VarSet.t option) (p:path) : path =
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


and priming_mem (pr:bool) (prime_set:VarSet.t option) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem(priming_variable pr prime_set v)
  | Update(mem,add,cell) -> Update(priming_mem pr prime_set mem,
                                   priming_addr pr prime_set add,
                                   priming_cell pr prime_set cell)
  | MemArrayRd(arr,t)    -> MemArrayRd(priming_array pr prime_set arr,
                                       priming_tid pr prime_set t)


and priming_int (pr:bool) (prime_set:VarSet.t option) (i:integer) : integer =
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



and priming_atom (pr:bool) (prime_set:VarSet.t option) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)         -> Append(priming_path pr prime_set p1,
                                         priming_path pr prime_set p2,
                                         priming_path pr prime_set pres)
  | Reach(h,add_from,add_to,p) -> Reach(priming_mem pr prime_set h,
                                        priming_addr pr prime_set add_from,
                                        priming_addr pr prime_set add_to,
                                        priming_path pr prime_set p)
  | ReachAt(h,a_from,a_to,l,p) -> ReachAt(priming_mem pr prime_set h,
                                          priming_addr pr prime_set a_from,
                                          priming_addr pr prime_set a_to,
                                          priming_int pr prime_set l,
                                          priming_path pr prime_set p)
  | OrderList(h,a_from,a_to)   -> OrderList(priming_mem pr prime_set h,
                                            priming_addr pr prime_set a_from,
                                            priming_addr pr prime_set a_to)
  | Skiplist(h,s,l,a_from,a_to)-> Skiplist(priming_mem pr prime_set h,
                                           priming_set pr prime_set s,
                                           priming_int pr prime_set l,
                                           priming_addr pr prime_set a_from,
                                           priming_addr pr prime_set a_to)
  | In(a,s)                    -> In(priming_addr pr prime_set a,
                                     priming_set pr prime_set s)
  | SubsetEq(s_in,s_out)       -> SubsetEq(priming_set pr prime_set s_in,
                                           priming_set pr prime_set s_out)
  | InTh(th,s)                 -> InTh(priming_tid pr prime_set th,
                                       priming_setth pr prime_set s)
  | SubsetEqTh(s_in,s_out)     -> SubsetEqTh(priming_setth pr prime_set s_in,
                                             priming_setth pr prime_set s_out)
  | InInt(i,s)                 -> InInt(priming_int pr prime_set i,
                                        priming_setint pr prime_set s)
  | SubsetEqInt(s_in,s_out)    -> SubsetEqInt(priming_setint pr prime_set s_in,
                                              priming_setint pr prime_set s_out)
  | InElem(e,s)                -> InElem(priming_elem pr prime_set e,
                                         priming_setelem pr prime_set s)
  | SubsetEqElem(s_in,s_out)   -> SubsetEqElem(priming_setelem pr prime_set s_in,
                                               priming_setelem pr prime_set s_out)
  | Less(i1,i2)                -> Less(priming_int pr prime_set i1,
                                       priming_int pr prime_set i2)
  | Greater(i1,i2)             -> Greater(priming_int pr prime_set i1,
                                          priming_int pr prime_set i2)
  | LessEq(i1,i2)              -> LessEq(priming_int pr prime_set i1,
                                         priming_int pr prime_set i2)
  | LessTid(t1,t2)             -> LessTid(priming_tid pr prime_set t1,
                                          priming_tid pr prime_set t2)
  | LessElem(e1,e2)            -> LessElem(priming_elem pr prime_set e1,
                                           priming_elem pr prime_set e2)
  | GreaterElem(e1,e2)         -> GreaterElem(priming_elem pr prime_set e1,
                                              priming_elem pr prime_set e2)
  | GreaterEq(i1,i2)           -> GreaterEq(priming_int pr prime_set i1,
                                            priming_int pr prime_set i2)
  | Eq(exp)                    -> Eq(priming_eq pr prime_set exp)
  | InEq(exp)                  -> InEq(priming_ineq pr prime_set exp)
  | BoolVar v                  -> BoolVar (priming_variable pr prime_set v)
  | BoolArrayRd (a,t)          -> BoolArrayRd (priming_array pr prime_set a,
                                               priming_tid pr prime_set t)
  | PC (pc,t,_)                -> PC (pc, t, pr)
  | PCUpdate (pc,t)            -> PCUpdate (pc,t)
  | PCRange (pc1,pc2,t,_)      -> PCRange (pc1, pc2, t, pr)


and priming_eq (pr:bool) (prime_set:VarSet.t option) ((t1,t2):eq) : eq =
  (priming_term pr prime_set t1, priming_term pr prime_set t2)


and priming_ineq (pr:bool) (prime_set:VarSet.t option) ((t1,t2):diseq) : diseq =
  (priming_term pr prime_set t1, priming_term pr prime_set t2)


and priming_literal (pr:bool) (prime_set:VarSet.t option) (l:literal) : literal=
  match l with
    Atom a    -> Atom (priming_atom pr prime_set a)
  | NegAtom a -> NegAtom (priming_atom pr prime_set a)


and priming_conjunctive_formula (pr:bool)
                                (prime_set:VarSet.t option)
                                (cf:conjunctive_formula) : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (priming_literal pr prime_set) ls)


and priming_formula (pr:bool) (prime_set:VarSet.t option) (phi:formula) : 
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

(* exported priming functions *)

let prime_addr (a:addr) : addr =
  priming_addr true None a

let unprime_addr (a:addr) : addr =
  priming_addr false None a


let prime_elem (e:elem) : elem =
  priming_elem true None e

let unprime_elem (e:elem) : elem =
  priming_elem false None e


let prime_cell (c:cell) : cell =
  priming_cell true None c

let unprime_cell (c:cell) : cell =
  priming_cell false None c


let prime_mem (m:mem) : mem =
  priming_mem true None m

let unprime_mem (m:mem) : mem =
  priming_mem false None m


let prime_int (i:integer) : integer =
  priming_int true None i

let unprime_int (i:integer) : integer =
  priming_int false None i


let prime_addrarr (aa:addrarr) : addrarr =
  priming_addrarray true None aa

let unprime_int (aa:addrarr) : addrarr =
  priming_addrarray false None aa


let prime_tidarr (tt:tidarr) : tidarr =
  priming_tidarray true None tt

let unprime_tidarr (tt:tidarr) : tidarr =
  priming_tidarray false None tt


let prime_term (t:term) : term =
  priming_term true None t

let unprime_term (t:term) : term =
  priming_term false None t


let prime_atom (a:atom) : atom =
  priming_atom true None a

let unprime_atom (a:atom) : atom =
  priming_atom false None a


let prime (phi:formula) : formula =
  priming_formula true None phi

let unprime (phi:formula) : formula =
  priming_formula false None phi


let prime_only (prime_set:VarSet.t) (phi:formula) : formula =
  priming_formula true (Some prime_set) phi

let unprime_only (prime_set:VarSet.t) (phi:formula) : formula =
  priming_formula false (Some prime_set) phi


let prime_term_only (prime_set:VarSet.t) (t:term) : term =
  priming_term true (Some prime_set) t

let unprime_term_only (prime_set:VarSet.t) (t:term) : term =
  priming_term false (Some prime_set) t 


let prime_option_tid (th:tid option) : tid option =
  priming_option_tid true None th

let unprime_option_tid (th:tid option) : tid option =
  priming_option_tid false None th

let prime_tid (th:tid) : tid =
  priming_tid true None th

let unprime_tid (th:tid) : tid =
  priming_tid false None th




(* PRINTING FUNCTIONS *)

(* variable_to_str fold function *)
let rec variable_to_str (var:variable) : string =
  let (id,s,pr,th,p,k) = var in
  let var_str = sprintf "%s%s" (loc_var_option id p) (tid_option_to_str th)
  in
    if pr then var_str ^ "'" else var_str


and variable_to_simple_str (var:variable) : string =
  let (id,s,pr,th,p,k) = var in
  let var_str = sprintf "%s%s" (loc_var_option id p) (tid_option_to_str th)
  in
    if pr then var_str ^ "'" else var_str


and tid_to_str (th:tid) : string =
  match th with
    VarTh v              -> variable_to_str v
  | NoThid               -> sprintf "#"
  | CellLockId(cell)     -> sprintf "%s.lockid" (cell_to_str cell)
  | CellLockIdAt(cell,l) -> sprintf "%s.lockid[%s]" (cell_to_str cell)
                                                    (integer_to_str l)
  | ThidArrayRd(arr,t)   -> sprintf "%s[%s]" (arrays_to_str arr)
                                             (param_tid_to_str t)
  | ThidArrRd(arr,l)     -> sprintf "%s[%s]" (tidarr_to_str arr)
                                             (integer_to_str l)


and param_tid_to_str (expr:tid) : string =
    match expr with
    VarTh v       -> let id = var_id v in
                     begin
                       try
                         sprintf "[%i]" (int_of_string id)
                       with
                         _ -> sprintf "(%s)" (variable_to_str v)
                     end
  | NoThid        -> sprintf "(#)"
  | CellLockId _  -> sprintf "(%s)" (tid_to_str expr)
  | CellLockIdAt _-> sprintf "(%s)" (tid_to_str expr)
  | ThidArrayRd _ -> sprintf "(%s)" (tid_to_str expr)
  | ThidArrRd _   -> sprintf "(%s)" (tid_to_str expr)


and tid_option_to_str (expr:tid option) : string =
  Option.map_default param_tid_to_str "" expr


and atom_to_str (expr:atom) : string =
  match expr with
    Append(p1,p2,pres)         -> sprintf "append(%s,%s,%s)"
                                            (path_to_str p1)
                                            (path_to_str p2)
                                            (path_to_str pres)
  | Reach(h,add_from,add_to,p) -> sprintf "reach(%s,%s,%s,%s)"
                                            (mem_to_str h)
                                            (addr_to_str add_from)
                                            (addr_to_str add_to)
                                            (path_to_str p)
  | ReachAt(h,a_from,a_to,l,p) -> sprintf "reach(%s,%s,%s,%s,%s)"
                                            (mem_to_str h)
                                            (addr_to_str a_from)
                                            (addr_to_str a_to)
                                            (integer_to_str l)
                                            (path_to_str p)
  | OrderList(h,a_from,a_to)   -> sprintf "orderlist(%s,%s,%s)"
                                            (mem_to_str h)
                                            (addr_to_str a_from)
                                            (addr_to_str a_to)
  | Skiplist(h,s,l,a_from,a_to)-> sprintf "skiplist(%s,%s,%s,%s,%s)"
                                            (mem_to_str h)
                                            (set_to_str s)
                                            (integer_to_str l)
                                            (addr_to_str a_from)
                                            (addr_to_str a_to)
  | In(a,s)                    -> sprintf "%s in %s "
                                            (addr_to_str a) (set_to_str s)
  | SubsetEq(s_in,s_out)       -> sprintf "%s subseteq %s"
                                            (set_to_str s_in)
                                            (set_to_str s_out)
  | InTh(th,s)                 -> sprintf "%s inTh %s"
                                            (tid_to_str th)
                                            (setth_to_str s)
  | SubsetEqTh(s_in,s_out)     -> sprintf "%s subseteqTh %s"
                                            (setth_to_str s_in)
                                            (setth_to_str s_out)
  | InInt(i,s)                 -> sprintf "%s inInt %s"
                                            (integer_to_str i)
                                            (setint_to_str s)
  | SubsetEqInt(s_in,s_out)    -> sprintf "%s subseteqInt %s"
                                            (setint_to_str s_in)
                                            (setint_to_str s_out)
  | InElem(e,s)                -> sprintf "%s inElem %s"
                                            (elem_to_str e)
                                            (setelem_to_str s)
  | SubsetEqElem(s_in,s_out)   -> sprintf "%s subseteqElem %s"
                                            (setelem_to_str s_in)
                                            (setelem_to_str s_out)
  | Less(i1,i2)                -> sprintf "%s < %s"
                                            (integer_to_str i1)
                                            (integer_to_str i2)
  | Greater(i1,i2)             -> sprintf "%s > %s"
                                            (integer_to_str i1)
                                            (integer_to_str i2)
  | LessEq(i1,i2)              -> sprintf "%s <= %s"
                                            (integer_to_str i1)
                                            (integer_to_str i2)
  | GreaterEq(i1,i2)           -> sprintf "%s >= %s"
                                            (integer_to_str i1)
                                            (integer_to_str i2)
  | LessTid(t1,t2)             -> sprintf "%s < %s"
                                            (tid_to_str t1)
                                            (tid_to_str t2)
  | LessElem(e1,e2)            -> sprintf "%s < %s"
                                            (elem_to_str e1)
                                            (elem_to_str e2)
  | GreaterElem(e1,e2)         -> sprintf "%s > %s"
                                            (elem_to_str e1)
                                            (elem_to_str e2)
  | Eq(exp)                    -> eq_to_str (exp)
  | InEq(exp)                  -> diseq_to_str (exp)
  | BoolVar v                  -> variable_to_str v
  | BoolArrayRd(arr,t)         -> sprintf "%s%s" (arrays_to_str arr)
                                                 (param_tid_to_str t)
  | PC (pc,t,p)                -> let t_str =
                                    if p then
                                      tid_option_to_str (prime_option_tid t)
                                    else
                                      tid_option_to_str t in
                                  let v_name =
                                    if p then
                                      prime_var_name pc_name
                                    else
                                      pc_name
                                  in
                                    sprintf "%s%s=%i" v_name t_str pc
  | PCUpdate (pc,t)            -> let t_str = tid_to_str t
                                  in
                                    sprintf"pc' = pc{%s<-%i}" t_str pc
  | PCRange (pc1,pc2,t,p)      -> let t_str =
                                    if p then
                                      tid_option_to_str (prime_option_tid t)
                                    else
                                      tid_option_to_str t in
                                  let v_name =
                                    if p then
                                      prime_var_name pc_name
                                    else
                                      pc_name
                                  in
                                    sprintf "%s%s = [%i,%i]" v_name t_str pc1 pc2


and literal_to_str (expr:literal) : string =
  match expr with
    Atom a    -> atom_to_str a
  | NegAtom a -> sprintf "~ %s" (atom_to_str a)


and arrays_to_str (expr:arrays) : string =
  match expr with
    VarArray v       -> variable_to_str v
  | ArrayUp(arr,t,e) -> sprintf "%s{%s<-%s}" (arrays_to_str arr)
                                             (tid_to_str t)
                                             (expr_to_str e)


and addrarr_to_str (expr:addrarr) : string =
  match expr with
    VarAddrArray v       -> variable_to_str v
  | AddrArrayUp(arr,i,a) -> sprintf "%s{%s<-%s}" (addrarr_to_str arr)
                                                 (integer_to_str i)
                                                 (addr_to_str a)
  | CellArr c            -> sprintf "%s.arr" (cell_to_str c)


and tidarr_to_str (expr:tidarr) : string =
  match expr with
    VarTidArray v       -> variable_to_str v
  | TidArrayUp(arr,i,t) -> sprintf "%s{%s<-%s}" (tidarr_to_str arr)
                                                (integer_to_str i)
                                                (tid_to_str t)
  | CellTids c            -> sprintf "%s.tids" (cell_to_str c)


and integer_to_str (expr:integer) : string =
  match expr with
    IntVal (i)        -> string_of_int i
  | VarInt v          -> variable_to_str v
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
    VarMem v             -> variable_to_str v
  | Update(mem,add,cell) -> sprintf "upd(%s,%s,%s)" (mem_to_str mem)
                                                    (addr_to_str add)
                                                    (cell_to_str cell)
  | MemArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str arr)
                                           (param_tid_to_str t)


and path_to_str (expr:path) : string =
  match expr with
    VarPath v                        -> variable_to_str v
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
    VarSet v            -> variable_to_str v
  | EmptySet            -> "EmptySet"
  | Singl(addr)         -> sprintf "{ %s }" (addr_to_str addr)
  | Union(s1,s2)        -> sprintf "%s Union %s" (set_to_str s1)
                                                 (set_to_str s2)
  | Intr(s1,s2)         -> sprintf "%s Intr %s" (set_to_str s1)
                                                (set_to_str s2)
  | Setdiff(s1,s2)      -> sprintf "%s SetDiff %s" (set_to_str s1)
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
    VarSetTh v          -> variable_to_str v
  | EmptySetTh          -> "EmptySetTh"
  | SinglTh(th)         -> sprintf "SinglTh(%s)" (tid_to_str th)
  | UnionTh(s_1,s_2)    -> sprintf "%s UnionTh %s" (setth_to_str s_1)
                                                   (setth_to_str s_2)
  | IntrTh(s_1,s_2)     -> sprintf "%s IntrTh %s" (setth_to_str s_1)
                                                  (setth_to_str s_2)
  | SetdiffTh(s_1,s_2)  -> sprintf "%s SetDiffTh %s" (setth_to_str s_1)
                                                     (setth_to_str s_2)
  | SetThArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                          (param_tid_to_str t)


and setint_to_str (expr:setint) : string =
  match expr with
    VarSetInt v          -> variable_to_str v
  | EmptySetInt          -> "EmptySetInt"
  | SinglInt(th)         -> sprintf "SinglInt(%s)" (integer_to_str th)
  | UnionInt(s_1,s_2)    -> sprintf "%s UnionInt %s" (setint_to_str s_1)
                                                     (setint_to_str s_2)
  | IntrInt(s_1,s_2)     -> sprintf "%s IntrInt %s" (setint_to_str s_1)
                                                    (setint_to_str s_2)
  | SetdiffInt(s_1,s_2)  -> sprintf "%s SetDiffInt %s" (setint_to_str s_1)
                                                       (setint_to_str s_2)
  | SetIntArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                           (param_tid_to_str t)


and setelem_to_str (expr:setelem) : string =
  match expr with
    VarSetElem v          -> variable_to_str v
  | EmptySetElem          -> "EmptySetElem"
  | SinglElem(e)          -> sprintf "SinglElem(%s)" (elem_to_str e)
  | UnionElem(s_1,s_2)    -> sprintf "%s UnionElem %s" (setelem_to_str s_1)
                                                       (setelem_to_str s_2)
  | IntrElem(s_1,s_2)     -> sprintf "%s IntrElem %s" (setelem_to_str s_1)
                                                      (setelem_to_str s_2)
  | SetdiffElem(s_1,s_2)  -> sprintf "%s SetDiffElem %s" (setelem_to_str s_1)
                                                         (setelem_to_str s_2)
  | SetToElems(s,m)       -> sprintf "SetToElems (%s,%s)" (set_to_str s)
                                                          (mem_to_str m)
  | SetElemArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                            (param_tid_to_str t)


and cell_to_str (expr:cell) : string =
  let list_str f xs = String.concat "," (List.map f xs) in
  match expr with
    VarCell v              -> variable_to_str v
  | Error                  -> "Error"
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
  | CellUnlockAt(cell,l)  -> sprintf "%s.unlock[%s]" (cell_to_str cell)
                                                     (integer_to_str l)
  | CellAt(mem,addr)      -> sprintf "rd(%s,%s)" (mem_to_str mem)
                                                 (addr_to_str addr)
  | CellArrayRd(arr,t)    -> sprintf "%s%s" (arrays_to_str arr)
                                            (param_tid_to_str t)


and addr_to_str (expr:addr) :string =
  match expr with
    VarAddr v                 -> variable_to_str v
  | Null                      -> "null"
  | Next(cell)                -> sprintf "%s.next" (cell_to_str cell)
  | NextAt(cell,l)            -> sprintf "%s.nextat[%s]" (cell_to_str cell)
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
    VarElem v          -> variable_to_str v
  | CellData(cell)     -> sprintf "%s.data" (cell_to_str cell)
  | ElemArrayRd(arr,t) -> sprintf "%s%s" (arrays_to_str arr)
                                         (param_tid_to_str t)
  | HavocListElem      -> "havocListElem()"
  | HavocSkiplistElem  -> "havocSLElem()"
  | LowestElem         -> "lowestElem"
  | HighestElem        -> "highestElem"


and term_to_str (expr:term) : string =
  match expr with
    VarT v            -> variable_to_str v
  | SetT(set)         -> (set_to_str set)
  | AddrT(addr)       -> (addr_to_str addr)
  | ElemT(elem)       -> (elem_to_str elem)
  | ThidT(th)         -> (tid_to_str th)
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


and conjunctive_formula_to_str (expr:conjunctive_formula) : string =
  match expr with
    FalseConj -> "false"
  | TrueConj  -> "true"
  | Conj ls   -> String.concat " /\\ " $ List.map literal_to_str ls


and formula_to_str (expr:formula) : string =
  match expr with
    Literal(lit)          -> (literal_to_str lit)
  | True                  -> sprintf "true"
  | False                 -> sprintf "false"
  | And(f1, f2)           -> sprintf "%s /\\ %s" (formula_to_str f1)
                                                 (formula_to_str f2)
  | Or(f1,f2)             -> sprintf "%s \\/ %s" (formula_to_str f1)
                                                 (formula_to_str f2)
  | Not(f)                -> sprintf "~ %s" (formula_to_str f)
  | Implies(f1,f2)        -> sprintf "%s -> %s" (formula_to_str f1)
                                                (formula_to_str f2)
  | Iff (f1,f2)           -> sprintf "%s <-> %s" (formula_to_str f1)
                                                 (formula_to_str f2)





(* THREAD IDENTIFIER INFORMATION FUNCTIONS *)
let is_tid_var (t:tid) : bool =
  match t with
    VarTh v -> begin
                 try
                   let _ = int_of_string (var_id v) in false
                 with
                   _ -> true
               end
  | _       -> false


let is_tid_val (t:tid) : bool =
  match t with
    VarTh v -> begin
                 try
                   let _ = int_of_string (var_id v) in true
                 with
                   _ -> false
               end
  | _       -> false


let is_tid_nolock (t:tid) : bool =
  match t with
    NoThid -> true
  | _      -> false


let is_tid_lockid (t:tid) : bool =
  match t with
    CellLockId _ -> true
  | _            -> false



(* VARIABLE INFORMATION FUNCTIONS *)
let var_info_sort ((s,_,_,_):var_info_t) : sort = s
let var_info_expr ((_,e,_,_):var_info_t) : initVal_t option = e
let var_info_tid  ((_,_,t,_):var_info_t) : tid option = t
let var_info_kind ((_,_,_,k):var_info_t) : kind_t = k


let get_var_info (t:term)
                    : varId * bool * tid option * string option * kind_t =
  let get_info v = (var_id v, var_pr v, var_th v, var_proc v, var_k v)
  in
  match t with
    VarT v                           -> get_info v
  | SetT(VarSet v)                   -> get_info v
  | ElemT(VarElem v)                 -> get_info v
  | ThidT(VarTh v)                   -> get_info v
  | AddrT(VarAddr v)                 -> get_info v
  | CellT(VarCell v)                 -> get_info v
  | SetThT(VarSetTh v)               -> get_info v
  | PathT(VarPath v)                 -> get_info v
  | MemT(VarMem v)                   -> get_info v
  | IntT(VarInt v)                   -> get_info v
  | ElemT(CellData(VarCell v))       -> get_info v
  | AddrT(Next(VarCell v))           -> get_info v
  | ThidT(CellLockId(VarCell v))     -> get_info v
  | CellT(CellLock(VarCell v,_))     -> get_info v
  | CellT(CellUnlock(VarCell v))     -> get_info v
  | CellT(CellLockAt(VarCell v,_,_)) -> get_info v
  | CellT(CellUnlockAt(VarCell v,_)) -> get_info v
  | _                                -> ("",false,None,None,Normal)


let get_var_id (t:term) : varId =
  let (v,_,_,_,_) = get_var_info t in v


let get_var_primed (t:term) : bool =
  let (_,pr,_,_,_) = get_var_info t in pr


let get_var_thread (t:term) : tid option =
  let (_,_,th,_,_) = get_var_info t in th


let get_var_owner (t:term) : string option =
  let (_,_,_,p,_) = get_var_info t in p


let get_var_kind (t:term) : kind_t =
  let (_,_,_,_,k) = get_var_info t in k



(* THREAD LIST GENERATION FUNCTIONS *)



let rec gen_thread_list (min:int) (max:int) : tid list =
  if min > max then
    []
  else
    (build_num_tid min) :: gen_thread_list (min+1) max


let rec gen_thread_list_except (min:int) (max:int) (t:tid) : tid list =
  if min > max then
    []
  else
    let new_th = build_num_tid min in
    if new_th <> t then
      new_th :: gen_thread_list_except (min+1) max t
    else
      gen_thread_list_except (min+1) max t


let gen_fresh_thread (xs:tid list) : tid =
  let rec find n =
    let th_cand_id = sprintf "k_%i" n in
    let th_cand = VarTh (build_var th_cand_id Thid false None None Normal)in
      if List.mem th_cand xs then find (n+1) else th_cand
  in
    find 0


let rec gen_fresh_thread_list (xs:tid list) (n:int) : tid list =
  match n with
    0 -> []
  | m -> let new_th = gen_fresh_thread xs in
           new_th :: (gen_fresh_thread_list (new_th::xs) (m-1))



(* PRINTING FUNCTIONS *)

let pc_to_str (p:pc_t) : string =
  string_of_int p


let sort_to_str (s:sort) : string =
  match s with
      Set       -> "set"
    | Elem      -> "elem"
    | Thid      -> "tid"
    | Addr      -> "addr"
    | Cell      -> "cell"
    | SetTh     -> "setTh"
    | SetInt    -> "setInt"
    | SetElem   -> "setElem"
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
          Iff (_,f) -> Formula f
        | Literal (Atom (In          (_,s))) -> Term (SetT s)
        | Literal (Atom (SubsetEq    (_,s))) -> Term (SetT s)
        | Literal (Atom (InTh        (_,s))) -> Term (SetThT s)
        | Literal (Atom (SubsetEqTh  (_,s))) -> Term (SetThT s)
        | Literal (Atom (InInt       (_,s))) -> Term (SetIntT s)
        | Literal (Atom (SubsetEqInt (_,s))) -> Term (SetIntT s)
        | Literal (Atom (Less        (_,i))) -> Term (IntT i)
        | Literal (Atom (Greater     (_,i))) -> Term (IntT i)
        | Literal (Atom (LessEq      (_,i))) -> Term (IntT i)
        | Literal (Atom (GreaterEq   (_,i))) -> Term (IntT i)
        | _ -> Interface.Err.msg "Invalid argument" $
                sprintf "Function get_initVal_restrictions was expecting a \
                         condition over integers or sets. Instead, \"%s\" was \
                         received." (formula_to_str c);
               RAISE(Invalid_argument)
      end


let term_to_integer (t:term) : integer =
  match t with
    IntT i -> i
  | _      -> Interface.Err.msg "Not an integer term" $
                sprintf "Impossible to convert to integer a non integer \
                         term. An integer term was expected, but \"%s\" was \
                         received." (term_to_str t);
              RAISE(Invalid_argument)


let term_to_set (t:term) : set =
  match t with
    SetT s -> s
  | _      -> Interface.Err.msg "Not a set term" $
                sprintf "Impossible to convert to set a non set \
                         term. A set term was expected, but \"%s\" was \
                         received." (term_to_str t);
              RAISE(Invalid_argument)


let term_to_setth (t:term) : setth =
  match t with
    SetThT s -> s
  | _        -> Interface.Err.msg "Not a set of thread identifiers term" $
                  sprintf "Impossible to convert to set of thread identifiers \
                           a non set of thread identifiers term. A set of \
                           thread identifiers term was expected, but \"%s\" \
                           was received." (term_to_str t);
                RAISE(Invalid_argument)


let term_to_setint (t:term) : setint =
  match t with
    SetIntT s -> s
  | _        -> Interface.Err.msg "Not a set of integers term" $
                  sprintf "Impossible to convert to set of integers \
                           a non set of integers term. A set of \
                            integers term was expected, but \"%s\" \
                           was received." (term_to_str t);
                RAISE(Invalid_argument)



(* PRIMING QUERY FUNCTIONS *)

let rec get_vars_term (expr:term)
                      (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match expr with
    VarT v            -> (base v)@(Option.map_default get_vars_aux [] (var_th v))
  | SetT(set)         -> get_vars_set set base
  | AddrT(addr)       -> get_vars_addr addr base
  | ElemT(elem)       -> get_vars_elem elem base
  | ThidT(th)         -> get_vars_tid th base
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


and get_vars_expr (e:expr_t)
                  (base:variable -> variable list) : variable list =
  match e with
    Term t    -> get_vars_term t base
  | Formula b -> get_vars_formula b base


and get_vars_array (a:arrays)
                   (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match a with
    VarArray v       -> (base v)@(Option.map_default get_vars_aux [] (var_th v))
  | ArrayUp(arr,t,e) -> (get_vars_array arr base) @
                        (get_vars_tid t base)     @
                        (get_vars_expr e base)


and get_vars_addrarr (a:addrarr)
                     (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match a with
    VarAddrArray v       -> (base v) @
                            (Option.map_default get_vars_aux [] (var_th v))
  | AddrArrayUp(arr,i,a) -> (get_vars_addrarr arr base) @
                            (get_vars_int i base)       @
                            (get_vars_addr a base)
  | CellArr c            -> (get_vars_cell c base)


and get_vars_tidarr (a:tidarr)
                    (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match a with
    VarTidArray v       -> (base v) @
                           (Option.map_default get_vars_aux [] (var_th v))
  | TidArrayUp(arr,i,t) -> (get_vars_tidarr arr base) @
                           (get_vars_int i base)      @
                           (get_vars_tid t base)
  | CellTids c            -> (get_vars_cell c base)


and get_vars_set (e:set)
                 (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match e with
    VarSet v            -> (base v) @
                           (Option.map_default get_vars_aux [] (var_th v))
  | EmptySet            -> []
  | Singl(addr)         -> (get_vars_addr addr base)
  | Union(s1,s2)        -> (get_vars_set s1 base) @ (get_vars_set s2 base)
  | Intr(s1,s2)         -> (get_vars_set s1 base) @ (get_vars_set s2 base)
  | Setdiff(s1,s2)      -> (get_vars_set s1 base) @ (get_vars_set s2 base)
  | PathToSet(path)     -> (get_vars_path path base)
  | AddrToSet(mem,addr) -> (get_vars_mem mem base)@(get_vars_addr addr base)
  | AddrToSetAt(mem,a,l)-> (get_vars_mem mem base) @
                           (get_vars_addr a base)  @
                           (get_vars_int l base)
  | SetArrayRd(arr,t)   -> (get_vars_array arr base)


and get_vars_addr (a:addr)
                  (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match a with
    VarAddr v                 -> (base v) @
                                  (Option.map_default get_vars_aux [] (var_th v))
  | Null                      -> []
  | Next(cell)                -> (get_vars_cell cell base)
  | NextAt(cell,l)            -> (get_vars_cell cell base) @ (get_vars_int l base)
  | FirstLocked(mem,path)     -> (get_vars_mem mem base) @ (get_vars_path path base)
  | FirstLockedAt(mem,path,l) -> (get_vars_mem mem base) @ (get_vars_path path base) @
                                 (get_vars_int l base)
  | AddrArrayRd(arr,t)        -> (get_vars_array arr base)
  | AddrArrRd(arr,i)          -> (get_vars_addrarr arr base) @ (get_vars_int i base)


and get_vars_elem (e:elem)
                  (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match e with
    VarElem v          -> (base v) @
                          (Option.map_default get_vars_aux [] (var_th v))
  | CellData(cell)     -> (get_vars_cell cell base)
  | ElemArrayRd(arr,t) -> (get_vars_array arr base)
  | HavocListElem      -> []
  | HavocSkiplistElem  -> []
  | LowestElem         -> []
  | HighestElem        -> []


and get_vars_tid (th:tid)
                 (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match th with
    VarTh v              -> (base v) @
                            (Option.map_default get_vars_aux [] (var_th v))
  | NoThid               -> []
  | CellLockId(cell)     -> (get_vars_cell cell base)
  | CellLockIdAt(cell,l) -> (get_vars_cell cell base) @ (get_vars_int l base)
  | ThidArrayRd(arr,t)   -> (get_vars_array arr base)
  | ThidArrRd(arr,l)     -> (get_vars_tidarr arr base) @ (get_vars_int l base)


and get_vars_cell (c:cell)
                  (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  let fold f xs = List.fold_left (fun ys x -> (f x base) @ ys) [] xs in
  match c with
    VarCell v              -> (base v) @
                              (Option.map_default get_vars_aux [] (var_th v))
  | Error                  -> []
  | MkCell(data,addr,th)   -> (get_vars_elem data base) @
                              (get_vars_addr addr base) @
                              (get_vars_tid th base)
  | MkSLKCell(data,aa,tt)  -> (get_vars_elem data base) @
                              (fold get_vars_addr aa)   @
                              (fold get_vars_tid tt)
  | MkSLCell(data,aa,ta,l) -> (get_vars_elem data base) @
                              (get_vars_addrarr aa base) @
                              (get_vars_tidarr ta base) @
                              (get_vars_int l base)
  | CellLock(cell,t)       -> (get_vars_cell cell base) @ (get_vars_tid t base)
  | CellLockAt(cell,l,t)   -> (get_vars_cell cell base) @
                              (get_vars_int l base)     @
                              (get_vars_tid t base)
  | CellUnlock(cell)       -> (get_vars_cell cell base)
  | CellUnlockAt(cell,l)   -> (get_vars_cell cell base) @
                              (get_vars_int l base)
  | CellAt(mem,addr)       -> (get_vars_mem mem base) @
                              (get_vars_addr addr base)
  | CellArrayRd(arr,t)     -> (get_vars_array arr base)


and get_vars_setth (s:setth)
                   (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match s with
    VarSetTh v          -> (base v) @
                           (Option.map_default get_vars_aux [] (var_th v))
  | EmptySetTh          -> []
  | SinglTh(th)         -> get_vars_tid th base
  | UnionTh(s1,s2)      -> (get_vars_setth s1 base)@(get_vars_setth s2 base)
  | IntrTh(s1,s2)       -> (get_vars_setth s1 base)@(get_vars_setth s2 base)
  | SetdiffTh(s1,s2)    -> (get_vars_setth s1 base)@(get_vars_setth s2 base)
  | SetThArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_setint (s:setint)
                    (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match s with
    VarSetInt v          -> (base v) @
                            (Option.map_default get_vars_aux [] (var_th v))
  | EmptySetInt          -> []
  | SinglInt(i)          -> (get_vars_int i base)
  | UnionInt(s1,s2)      -> (get_vars_setint s1 base) @
                            (get_vars_setint s2 base)
  | IntrInt(s1,s2)       -> (get_vars_setint s1 base) @
                            (get_vars_setint s2 base)
  | SetdiffInt(s1,s2)    -> (get_vars_setint s1 base) @
                            (get_vars_setint s2 base)
  | SetIntArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_setelem (s:setelem)
                     (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match s with
    VarSetElem v          -> (base v) @
                             (Option.map_default get_vars_aux [] (var_th v))
  | EmptySetElem          -> []
  | SinglElem(e)          -> (get_vars_elem e base)
  | UnionElem(s1,s2)      -> (get_vars_setelem s1 base) @
                             (get_vars_setelem s2 base)
  | IntrElem(s1,s2)       -> (get_vars_setelem s1 base) @
                             (get_vars_setelem s2 base)
  | SetdiffElem(s1,s2)    -> (get_vars_setelem s1 base) @
                             (get_vars_setelem s2 base)
  | SetToElems(s,m)       -> (get_vars_set s base) @ (get_vars_mem m base)
  | SetElemArrayRd(arr,t) -> (get_vars_array arr base)


and get_vars_path (p:path)
                  (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match p with
    VarPath v -> (base v) @ (Option.map_default get_vars_aux [] (var_th v))
  | Epsilon                          -> []
  | SimplePath(addr)                 -> (get_vars_addr addr base)
  | GetPath(mem,add_from,add_to)     -> (get_vars_mem mem base) @
                                        (get_vars_addr add_from base) @
                                        (get_vars_addr add_to base)
  | GetPathAt(mem,add_from,add_to,l) -> (get_vars_mem mem base) @
                                        (get_vars_addr add_from base) @
                                        (get_vars_addr add_to base) @
                                        (get_vars_int l base)
  | PathArrayRd(arr,t)               -> (get_vars_array arr base)


and get_vars_mem (m:mem)
                 (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match m with
    VarMem v             -> (base v) @
                            (Option.map_default get_vars_aux [] (var_th v))
  | Update(mem,add,cell) -> (get_vars_mem mem base) @
                            (get_vars_addr add base) @
                            (get_vars_cell cell base)
  | MemArrayRd(arr,t)    -> (get_vars_array arr base)


and get_vars_int (i:integer)
                 (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match i with
    IntVal(i)         -> []
  | VarInt v          -> (base v) @
                         (Option.map_default get_vars_aux [] (var_th v))
  | IntNeg(i)         -> (get_vars_int i base)
  | IntAdd(i1,i2)     -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | IntSub(i1,i2)     -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | IntMul(i1,i2)     -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | IntDiv(i1,i2)     -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | IntArrayRd(arr,t) -> (get_vars_array arr base)
  | IntSetMin(s)      -> (get_vars_setint s base)
  | IntSetMax(s)      -> (get_vars_setint s base)
  | CellMax(c)        -> (get_vars_cell c base)
  | HavocLevel        -> []


and get_vars_atom (a:atom)
                  (base:variable -> variable list) : variable list =
  let get_vars_aux t = get_vars_tid t base in
  match a with
    Append(p1,p2,pres)         -> (get_vars_path p1 base) @
                                  (get_vars_path p2 base) @
                                  (get_vars_path pres base)
  | Reach(h,add_from,add_to,p) -> (get_vars_mem h base) @
                                  (get_vars_addr add_from base) @
                                  (get_vars_addr add_to base) @
                                  (get_vars_path p base)
  | ReachAt(h,a_from,a_to,l,p) -> (get_vars_mem h base) @
                                  (get_vars_addr a_from base) @
                                  (get_vars_addr a_to base) @
                                  (get_vars_int l base) @
                                  (get_vars_path p base)
  | OrderList(h,a_from,a_to)   -> (get_vars_mem h base) @
                                  (get_vars_addr a_from base) @
                                  (get_vars_addr a_to base)
  | Skiplist(h,s,l,a_from,a_to)-> (get_vars_mem h base) @
                                  (get_vars_set s base) @
                                  (get_vars_int l base) @
                                  (get_vars_addr a_from base) @
                                  (get_vars_addr a_to base)
  | In(a,s)                    -> (get_vars_addr a base) @ (get_vars_set s base)
  | SubsetEq(s_in,s_out)       -> (get_vars_set s_in base) @
                                  (get_vars_set s_out base)
  | InTh(th,s)                 -> (get_vars_tid th base)@(get_vars_setth s base)
  | SubsetEqTh(s_in,s_out)     -> (get_vars_setth s_in base) @
                                  (get_vars_setth s_out base)
  | InInt(i,s)                 -> (get_vars_int i base) @
                                  (get_vars_setint s base)
  | SubsetEqInt(s_in,s_out)    -> (get_vars_setint s_in base) @
                                  (get_vars_setint s_out base)
  | InElem(e,s)                -> (get_vars_elem e base) @
                                  (get_vars_setelem s base)
  | SubsetEqElem(s_in,s_out)   -> (get_vars_setelem s_in base) @
                                  (get_vars_setelem s_out base)
  | Less(i1,i2)                -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | Greater(i1,i2)             -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | LessEq(i1,i2)              -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | GreaterEq(i1,i2)           -> (get_vars_int i1 base) @ (get_vars_int i2 base)
  | LessTid(t1,t2)             -> (get_vars_tid t1 base) @ (get_vars_tid t2 base)
  | LessElem(e1,e2)            -> (get_vars_elem e1 base) @ (get_vars_elem e2 base)
  | GreaterElem(e1,e2)         -> (get_vars_elem e1 base) @ (get_vars_elem e2 base)
  | Eq(exp)                    -> (get_vars_eq exp base)
  | InEq(exp)                  -> (get_vars_ineq exp base)
  | BoolVar v                  -> (base v) @
                                (Option.map_default get_vars_aux [] (var_th v))
  | BoolArrayRd(arr,t)         -> (get_vars_array arr base)
  | PC (pc,t,_)                -> Option.map_default get_vars_aux [] t
  | PCUpdate (pc,t)            -> get_vars_aux t
  | PCRange (pc1,pc2,t,_)      -> Option.map_default get_vars_aux [] t


and get_vars_eq ((t1,t2):eq) (base:variable -> variable list) : variable list =
  (get_vars_term t1 base) @ (get_vars_term t2 base)


and get_vars_ineq ((t1,t2):diseq)
                   (base:variable -> variable list) : variable list =
  (get_vars_term t1 base) @ (get_vars_term t2 base)


and get_vars_literal (l:literal)
                     (base:variable -> variable list) : variable list =
  match l with
    Atom a    -> get_vars_atom a base
  | NegAtom a -> get_vars_atom a base


and get_vars_conjunctive_formula (phi:conjunctive_formula)
                                 (base:variable -> variable list)
                                    : variable list =
  match phi with
    FalseConj -> []
  | TrueConj  -> []
  | Conj ls   -> List.fold_left (fun xs l -> (get_vars_literal l base)@xs) [] ls


and get_vars_formula (phi:formula)
                     (base:variable -> variable list) : variable list =
  match phi with
    Literal(lit)          -> (get_vars_literal lit base)
  | True                  -> []
  | False                 -> []
  | And(f1,f2)            -> (get_vars_formula f1 base) @
                             (get_vars_formula f2 base)
  | Or(f1,f2)             -> (get_vars_formula f1 base) @
                             (get_vars_formula f2 base)
  | Not(f)                -> (get_vars_formula f base)
  | Implies(f1,f2)        -> (get_vars_formula f1 base) @
                             (get_vars_formula f2 base)
  | Iff (f1,f2)           -> (get_vars_formula f1 base) @
                             (get_vars_formula f2 base)


(* Exported vars functions *)

let get_vars_as_set (phi:formula) (base:variable -> variable list) : VarSet.t =
  let var_list = get_vars_formula phi base in
  let var_set = List.fold_left (fun set v ->
                                  VarSet.add (unprime_variable v) set
                               ) (VarSet.empty) (var_list)
  in
    var_set


let get_vars (phi:formula) (base:variable -> variable list) : variable list =
  VarSet.elements (get_vars_as_set phi base)


let primed_vars (f:formula) : variable list =
  get_vars f (fun v -> if is_primed v then [v] else [])


let all_vars (f:formula) : variable list =
  get_vars f (fun v -> [v])


let all_vars_as_set (f:formula) : VarSet.t =
  get_vars_as_set f (fun v -> [v])


let all_local_vars (f:formula) : variable list =
  get_vars f (fun v -> if is_local_var v then [v] else [])


let all_local_owned_vars (f:formula) : variable list =
  get_vars f (fun v -> if is_owned_var v then [v] else [])


let all_global_vars (f:formula) : variable list =
  get_vars f (fun v -> if is_global_var v then [v] else [])


(* Primes in phi the variables modified in ante *)
let prime_modified (ante:formula) (phi:formula) : formula =
  LOG "Entering prime_modified" LEVEL TRACE;
  let p_vars = primed_vars ante in
  let p_set  = construct_var_set p_vars
  in
    prime_only p_set phi


let prime_modified_term (ante:formula) (t:term) : term =
  let p_vars = primed_vars ante in
  let p_set  = construct_var_set p_vars
  in
    prime_term_only p_set t




(* CONVERSION FUNCTIONS *)

let rec array_var_from_term (t:term) (prime:bool) : arrays =
  let modif_var v = let old_pr = var_pr v in
                      set_var_pr v (old_pr||prime) in
  match t with
    VarT v                       -> VarArray (modif_var v)
  | SetT(VarSet v)               -> VarArray (modif_var v)
  | ElemT(VarElem v)             -> VarArray (modif_var v)
  | ThidT(VarTh v)               -> VarArray (modif_var v)
  | AddrT(VarAddr v)             -> VarArray (modif_var v)
  | CellT(VarCell v)             -> VarArray (modif_var v)
  | SetThT(VarSetTh v)           -> VarArray (modif_var v)
  | PathT(VarPath v)             -> VarArray (modif_var v)
  | MemT(VarMem v)               -> VarArray (modif_var v)
  | IntT(VarInt v)               -> VarArray (modif_var v)
  | ArrayT(VarArray v)           -> VarArray (modif_var v)
  | ElemT(CellData(VarCell v))   -> VarArray (modif_var v)
  | AddrT(Next(VarCell v))       -> VarArray (modif_var v)
  | ThidT(CellLockId(VarCell v)) -> VarArray (modif_var v)
  | _ -> Interface.Err.msg "Invalid argument" $
           sprintf "A non variable or cell field term was \
                    passed to function \"array_var_from_term\". \
                    A variable was expected, but \"%s\" was given."
                    (term_to_str t);
         RAISE(Invalid_argument)


(* FIX: Replace by variable *)
let construct_var_from_sort (id:varId)
                            (th_p:tid option)
                            (p_name:string option)
                            (s:sort)
                            (k:kind_t) : term =
  let v = build_var id s false th_p p_name k in
  match s with
    Set       -> SetT       (VarSet       v)
  | Elem      -> ElemT      (VarElem      v)
  | Thid      -> ThidT      (VarTh        v)
  | Addr      -> AddrT      (VarAddr      v)
  | Cell      -> CellT      (VarCell      v)
  | SetTh     -> SetThT     (VarSetTh     v)
  | SetInt    -> SetIntT    (VarSetInt    v)
  | SetElem   -> SetElemT   (VarSetElem   v)
  | Path      -> PathT      (VarPath      v)
  | Mem       -> MemT       (VarMem       v)
  | Bool      -> VarT       v
  | Int       -> IntT       (VarInt       v)
  | Array     -> ArrayT     (VarArray     v)
  | AddrArray -> AddrArrayT (VarAddrArray v)
  | TidArray  -> TidArrayT  (VarTidArray  v)
  | Unknown   -> VarT       v


(* Converts a variable to a term *)
let convert_var_to_term (p:string option) (id:varId) (info:var_info_t) : term =
  let (s,e,t,k) = info
  in
    construct_var_from_sort id t p s k



(* Returns scope of a term. If the term is a variable, returns:
    Some "" if is a global variable declaration
    Some p if is a local declaration to process p
    None if the term is not a variable and thus it couldn't be determined *)
let get_term_scope (t:term) : string option =
  try
    let p = var_proc (term_to_var t) in
    match p with
      None -> Some ""
    | _    -> p
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
  let cons_array s v_term =
    let v_id = get_var_id v_term in
    let pr = get_var_primed v_term in
    let p = get_var_owner v_term in
    let k = get_var_kind v_term in
    let v_arr = VarArray(v_id, s, pr, None, p, k) in
      v_arr
  in
  match e with
    Some (Equality t) ->
      begin
        match s with
          Set   -> [eq_term (SetT   (SetArrayRd   (arr, th_p))) t]
        | Elem  -> [eq_term (ElemT  (ElemArrayRd  (arr, th_p))) t]
        | Thid  -> [eq_term (ThidT  (ThidArrayRd  (arr, th_p))) t]
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
                   RAISE(Invalid_argument)
      end
  | Some (Condition c) ->
    begin
      match c with
        Iff (Literal (Atom (BoolVar v)), f) ->
          [Iff(Literal(Atom(BoolArrayRd (VarArray(var_clear_param_info v), th_p))), f)]
      | Literal (Atom (In (a,s)))           ->
          [exp_in (AddrArrayRd(cons_array Addr (AddrT a), th_p)) s]
      | Literal (Atom (SubsetEq (s1,s2)))   ->
          [exp_subset (SetArrayRd (cons_array Set (SetT s1), th_p)) s2]
      | Literal (Atom (InTh (t,s)))         ->
          [exp_inth (ThidArrayRd(cons_array Thid (ThidT t), th_p)) s]
      | Literal (Atom (SubsetEqTh (s1,s2))) ->
          [exp_subsetth (SetThArrayRd (cons_array SetTh (SetThT s1),th_p)) s2]
      | Literal (Atom (InInt (i,s)))        ->
          [exp_inint (IntArrayRd (cons_array Int (IntT i), th_p)) s]
      | Literal (Atom (SubsetEqInt (s1,s2))) ->
          [exp_subsetint(SetIntArrayRd(cons_array SetInt (SetIntT s1),th_p)) s2]
      | Literal (Atom (Less (i1,i2)))       ->
          [exp_less (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | Literal (Atom (Greater (i1,i2)))    ->
          [exp_greater (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | Literal (Atom (LessEq (i1,i2)))     ->
          [exp_lesseq (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | Literal (Atom (GreaterEq (i1,i2)))  ->
          [exp_greatereq (IntArrayRd (cons_array Int (IntT i1), th_p)) i2]
      | _                                   -> [c]
    end
  | None -> []


(* VOCABULARY FUNCTIONS *)
let rec voc_term (expr:term) : tid list =
  match expr with
    VarT v -> (match var_sort v with
                  Thid -> [VarTh v]
                | _    -> []
              ) @ Option.map_default (fun x->[x]) [] (var_th v)
    | SetT(set)         -> voc_set set
    | AddrT(addr)       -> voc_addr addr
    | ElemT(elem)       -> voc_elem elem
    | ThidT(th)         -> voc_tid th
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


and voc_expr (e:expr_t) : tid list =
  match e with
    Term t    -> voc_term t
  | Formula b -> voc_formula b


and voc_array (a:arrays) : tid list =
  match a with
    VarArray v       -> Option.map_default (fun x->[x]) [] (var_th v)
  | ArrayUp(arr,t,e) -> (voc_array arr) @ (voc_expr e)


and voc_addrarr (a:addrarr) : tid list =
  match a with
    VarAddrArray v       -> Option.map_default (fun x->[x]) [] (var_th v)
  | AddrArrayUp(arr,i,a) -> (voc_addrarr arr) @ (voc_int i) @ (voc_addr a)
  | CellArr c            -> (voc_cell c)


and voc_tidarr (a:tidarr) : tid list =
  match a with
    VarTidArray v       -> Option.map_default (fun x->[x]) [] (var_th v)
  | TidArrayUp(arr,i,t) -> (voc_tidarr arr) @ (voc_int i) @ (voc_tid t)
  | CellTids c            -> (voc_cell c)


and voc_set (e:set) : tid list =
  match e with
    VarSet v             -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySet             -> []
  | Singl(addr)          -> (voc_addr addr)
  | Union(s1,s2)         -> (voc_set s1) @ (voc_set s2)
  | Intr(s1,s2)          -> (voc_set s1) @ (voc_set s2)
  | Setdiff(s1,s2)       -> (voc_set s1) @ (voc_set s2)
  | PathToSet(path)      -> (voc_path path)
  | AddrToSet(mem,addr)  -> (voc_mem mem) @ (voc_addr addr)
  | AddrToSetAt(mem,a,l) -> (voc_mem mem) @ (voc_addr a) @ (voc_int l)
  | SetArrayRd(arr,t)    -> (voc_array arr)


and voc_addr (a:addr) : tid list =
  match a with
    VarAddr v                 -> Option.map_default (fun x->[x]) [] (var_th v)
  | Null                      -> []
  | Next(cell)                -> (voc_cell cell)
  | NextAt(cell,l)            -> (voc_cell cell) @ (voc_int l)
  | FirstLocked(mem,path)     -> (voc_mem mem) @ (voc_path path)
  | FirstLockedAt(mem,path,l) -> (voc_mem mem) @ (voc_path path) @ (voc_int l)
  | AddrArrayRd(arr,t)        -> (voc_array arr)
  | AddrArrRd(arr,l)          -> (voc_addrarr arr) @ (voc_int l)


and voc_elem (e:elem) : tid list =
  match e with
    VarElem v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | CellData(cell)     -> (voc_cell cell)
  | ElemArrayRd(arr,t) -> (voc_array arr)
  | HavocListElem      -> []
  | HavocSkiplistElem  -> []
  | LowestElem         -> []
  | HighestElem        -> []


and voc_tid (th:tid) : tid list =
  match th with
    VarTh v              -> th::(Option.map_default (fun x->[x]) [] (var_th v))
  | NoThid               -> []
  | CellLockId(cell)     -> (voc_cell cell)
  | CellLockIdAt(cell,l) -> (voc_cell cell) @ (voc_int l)
  | ThidArrayRd(arr,t)   -> (voc_array arr)
  | ThidArrRd(arr,l)     -> (voc_tidarr arr) @ (voc_int l)


and voc_cell (c:cell) : tid list =
  let fold f xs = List.fold_left (fun ys x -> (f x) @ ys) [] xs in
  match c with
    VarCell v              -> Option.map_default (fun x->[x]) [] (var_th v)
  | Error                  -> []
  | MkCell(data,addr,th)   -> (voc_elem data) @
                              (voc_addr addr) @
                              (voc_tid th)
  | MkSLKCell(data,aa,tt)  -> (voc_elem data)    @
                              (fold voc_addr aa) @
                              (fold voc_tid tt)
  | MkSLCell(data,aa,ta,l) -> (voc_elem data)  @
                              (voc_addrarr aa) @
                              (voc_tidarr ta ) @
                              (voc_int l)
  | CellLock(cell,t)       -> (voc_cell cell) @ (voc_tid t)
  | CellLockAt(cell,l,t)   -> (voc_cell cell) @ (voc_int l) @ (voc_tid t)
  | CellUnlock(cell)       -> (voc_cell cell)
  | CellUnlockAt(cell,l)   -> (voc_cell cell) @ (voc_int l)
  | CellAt(mem,addr)       -> (voc_mem mem) @ (voc_addr addr)
  | CellArrayRd(arr,t)     -> (voc_array arr)


and voc_setth (s:setth) : tid list =
  match s with
    VarSetTh v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySetTh          -> []
  | SinglTh(th)         -> (voc_tid th)
  | UnionTh(s1,s2)      -> (voc_setth s1) @ (voc_setth s2)
  | IntrTh(s1,s2)       -> (voc_setth s1) @ (voc_setth s2)
  | SetdiffTh(s1,s2)    -> (voc_setth s1) @ (voc_setth s2)
  | SetThArrayRd(arr,t) -> (voc_array arr)


and voc_setint (s:setint) : tid list =
  match s with
    VarSetInt v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySetInt          -> []
  | SinglInt(th)         -> (voc_int th)
  | UnionInt(s1,s2)      -> (voc_setint s1) @ (voc_setint s2)
  | IntrInt(s1,s2)       -> (voc_setint s1) @ (voc_setint s2)
  | SetdiffInt(s1,s2)    -> (voc_setint s1) @ (voc_setint s2)
  | SetIntArrayRd(arr,t) -> (voc_array arr)


and voc_setelem (s:setelem) : tid list =
  match s with
    VarSetElem v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | EmptySetElem          -> []
  | SinglElem(e)          -> (voc_elem e)
  | UnionElem(s1,s2)      -> (voc_setelem s1) @ (voc_setelem s2)
  | IntrElem(s1,s2)       -> (voc_setelem s1) @ (voc_setelem s2)
  | SetdiffElem(s1,s2)    -> (voc_setelem s1) @ (voc_setelem s2)
  | SetToElems(s,m)       -> (voc_set s) @ (voc_mem m)
  | SetElemArrayRd(arr,t) -> (voc_array arr)


and voc_path (p:path) : tid list =
  match p with
    VarPath v                    -> Option.map_default (fun x->[x]) [] (var_th v)
  | Epsilon                      -> []
  | SimplePath(addr)             -> (voc_addr addr)
  | GetPath(mem,a_from,a_to)     -> (voc_mem mem) @
                                    (voc_addr a_from) @
                                    (voc_addr a_to)
  | GetPathAt(mem,a_from,a_to,l) -> (voc_mem mem) @
                                    (voc_addr a_from) @
                                    (voc_addr a_to) @
                                    (voc_int l)
  | PathArrayRd(arr,t)           -> (voc_array arr)


and voc_mem (m:mem) : tid list =
  match m with
    VarMem v             -> Option.map_default (fun x->[x]) [] (var_th v)
  | Update(mem,add,cell) -> (voc_mem mem) @ (voc_addr add) @ (voc_cell cell)
  | MemArrayRd(arr,t)    -> (voc_array arr)


and voc_int (i:integer) : tid list =
  match i with
    IntVal(i)         -> []
  | VarInt v          -> Option.map_default (fun x->[x]) [] (var_th v)
  | IntNeg(i)         -> (voc_int i)
  | IntAdd(i1,i2)     -> (voc_int i1) @ (voc_int i2)
  | IntSub(i1,i2)     -> (voc_int i1) @ (voc_int i2)
  | IntMul(i1,i2)     -> (voc_int i1) @ (voc_int i2)
  | IntDiv(i1,i2)     -> (voc_int i1) @ (voc_int i2)
  | IntArrayRd(arr,t) -> (voc_array arr)
  | IntSetMin(s)      -> (voc_setint s)
  | IntSetMax(s)      -> (voc_setint s)
  | CellMax(c)        -> (voc_cell c)
  | HavocLevel        -> []


and voc_atom (a:atom) : tid list =
  match a with
    Append(p1,p2,pres)         -> (voc_path p1) @
                                  (voc_path p2) @
                                  (voc_path pres)
  | Reach(h,add_from,add_to,p) -> (voc_mem h) @
                                  (voc_addr add_from) @
                                  (voc_addr add_to) @
                                  (voc_path p)
  | ReachAt(h,a_from,a_to,l,p) -> (voc_mem h) @
                                  (voc_addr a_from) @
                                  (voc_addr a_to) @
                                  (voc_int l) @
                                  (voc_path p)
  | OrderList(h,a_from,a_to)   -> (voc_mem h) @
                                  (voc_addr a_from) @
                                  (voc_addr a_to)
  | Skiplist(h,s,l,a_from,a_to)-> (voc_mem h) @
                                  (voc_set s) @
                                  (voc_int l) @
                                  (voc_addr a_from) @
                                  (voc_addr a_to)
  | In(a,s)                    -> (voc_addr a) @ (voc_set s)
  | SubsetEq(s_in,s_out)       -> (voc_set s_in) @ (voc_set s_out)
  | InTh(th,s)                 -> (voc_tid th) @ (voc_setth s)
  | SubsetEqTh(s_in,s_out)     -> (voc_setth s_in) @ (voc_setth s_out)
  | InInt(i,s)                 -> (voc_int i) @ (voc_setint s)
  | SubsetEqInt(s_in,s_out)    -> (voc_setint s_in) @ (voc_setint s_out)
  | InElem(e,s)                -> (voc_elem e) @ (voc_setelem s)
  | SubsetEqElem(s_in,s_out)   -> (voc_setelem s_in) @ (voc_setelem s_out)
  | Less(i1,i2)                -> (voc_int i1) @ (voc_int i2)
  | Greater(i1,i2)             -> (voc_int i1) @ (voc_int i2)
  | LessEq(i1,i2)              -> (voc_int i1) @ (voc_int i2)
  | GreaterEq(i1,i2)           -> (voc_int i1) @ (voc_int i2)
  | LessTid(t1,t2)             -> (voc_tid t1) @ (voc_tid t2)
  | LessElem(e1,e2)            -> (voc_elem e1) @ (voc_elem e2)
  | GreaterElem(e1,e2)         -> (voc_elem e1) @ (voc_elem e2)
  | Eq(exp)                    -> (voc_eq exp)
  | InEq(exp)                  -> (voc_ineq exp)
  | BoolVar v                  -> Option.map_default (fun x->[x]) [] (var_th v)
  | BoolArrayRd(arr,t)         -> (voc_array arr)
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


let unprimed_voc (phi:formula) : tid list =
  let voc_set = ThreadSet.filter (is_primed_tid>>not) (all_voc phi)
  in
    ThreadSet.elements voc_set




(* GHOST TERMS *)
let rec var_kind_term (kind:kind_t) (expr:term) : term list =
  match expr with
      VarT v            -> if (var_k v) = kind then [expr] else []
    | SetT(set)         -> var_kind_set kind set
    | AddrT(addr)       -> var_kind_addr kind addr
    | ElemT(elem)       -> var_kind_elem kind elem
    | ThidT(th)         -> var_kind_tid kind th
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


and var_kind_expr (kind:kind_t) (e:expr_t) : term list =
  match e with
    Term t    -> var_kind_term kind t
  | Formula b -> var_kind_formula kind b


and var_kind_array (kind:kind_t) (a:arrays) : term list =
  match a with
    VarArray v       -> if (var_k v) = kind then [ArrayT a] else []
  | ArrayUp(arr,t,e) -> (var_kind_array kind arr) @ (var_kind_expr kind e)


and var_kind_addrarr (kind:kind_t) (a:addrarr) : term list =
  match a with
    VarAddrArray v       -> if (var_k v) = kind then [AddrArrayT a] else []
  | AddrArrayUp(arr,i,a) -> (var_kind_addrarr kind arr) @
                            (var_kind_int kind i)       @
                            (var_kind_addr kind a)
  | CellArr c            -> (var_kind_cell kind c)


and var_kind_tidarr (kind:kind_t) (a:tidarr) : term list =
  match a with
    VarTidArray v       -> if (var_k v) = kind then [TidArrayT a] else []
  | TidArrayUp(arr,i,t) -> (var_kind_tidarr kind arr) @
                           (var_kind_int kind i)      @
                           (var_kind_tid kind t)
  | CellTids c            -> (var_kind_cell kind c)


and var_kind_set (kind:kind_t) (e:set) : term list =
  match e with
    VarSet v            -> if (var_k v) = kind then [SetT e] else []
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


and var_kind_addr (kind:kind_t) (a:addr) : term list =
  match a with
    VarAddr v                 -> if (var_k v) = kind then [AddrT a] else []
  | Null                      -> []
  | Next(cell)                -> (var_kind_cell kind cell)
  | NextAt(cell,l)            -> (var_kind_cell kind cell) @ (var_kind_int kind l)
  | FirstLocked(mem,path)     -> (var_kind_mem kind mem) @
                                 (var_kind_path kind path)
  | FirstLockedAt(mem,path,l) -> (var_kind_mem kind mem)   @
                                 (var_kind_path kind path) @
                                 (var_kind_int kind l)
  | AddrArrayRd(arr,t)        -> (var_kind_array kind arr)
  | AddrArrRd(arr,l)          -> (var_kind_addrarr kind arr) @ (var_kind_int kind l)


and var_kind_elem (kind:kind_t) (e:elem) : term list =
  match e with
    VarElem v          -> if (var_k v) = kind then [ElemT e] else []
  | CellData(cell)     -> (var_kind_cell kind cell)
  | ElemArrayRd(arr,t) -> (var_kind_array kind arr)
  | HavocListElem      -> []
  | HavocSkiplistElem  -> []
  | LowestElem         -> []
  | HighestElem        -> []


and var_kind_tid (kind:kind_t) (th:tid) : term list =
  match th with
    VarTh v              -> if (var_k v) = kind then [ThidT th] else []
  | NoThid               -> []
  | CellLockId(cell)     -> (var_kind_cell kind cell)
  | CellLockIdAt(cell,l) -> (var_kind_cell kind cell) @ (var_kind_int kind l)
  | ThidArrayRd(arr,t)   -> (var_kind_array kind arr)
  | ThidArrRd(arr,l)     -> (var_kind_tidarr kind arr) @ (var_kind_int kind l)


and var_kind_cell (kind:kind_t) (c:cell) : term list =
  let fold f xs = List.fold_left (fun ys x -> (f kind x) @ ys) [] xs in
  match c with
    VarCell v              -> if (var_k v) = kind then [CellT c] else []
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


and var_kind_setth (kind:kind_t) (s:setth) : term list =
  match s with
    VarSetTh v          -> if (var_k v) = kind then [SetThT s] else []
  | EmptySetTh          -> []
  | SinglTh(th)         -> (var_kind_tid kind th)
  | UnionTh(s1,s2)      -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | IntrTh(s1,s2)       -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetdiffTh(s1,s2)    -> (var_kind_setth kind s1) @ (var_kind_setth kind s2)
  | SetThArrayRd(arr,t) -> (var_kind_array kind arr)


and var_kind_setint (kind:kind_t) (s:setint) : term list =
  match s with
    VarSetInt v          -> if (var_k v) = kind then [SetIntT s] else []
  | EmptySetInt          -> []
  | SinglInt(i)          -> (var_kind_int kind i)
  | UnionInt(s1,s2)      -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | IntrInt(s1,s2)       -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetdiffInt(s1,s2)    -> (var_kind_setint kind s1) @
                            (var_kind_setint kind s2)
  | SetIntArrayRd(arr,t) -> (var_kind_array kind arr)


and var_kind_setelem (kind:kind_t) (s:setelem) : term list =
  match s with
    VarSetElem v          -> if (var_k v) = kind then [SetElemT s] else []
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


and var_kind_path (kind:kind_t) (p:path) : term list =
  match p with
    VarPath v                        -> if (var_k v)= kind then [PathT p] else []
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


and var_kind_mem (kind:kind_t) (m:mem) : term list =
  match m with
    VarMem v             -> if (var_k v) = kind then [MemT m] else []
  | Update(mem,add,cell) -> (var_kind_mem kind mem) @
                            (var_kind_addr kind add) @
                            (var_kind_cell kind cell)
  | MemArrayRd(arr,t)    -> (var_kind_array kind arr)


and var_kind_int (kind:kind_t) (i:integer) : term list =
  match i with
    IntVal(i)         -> []
  | VarInt v          -> if (var_k v) = kind then [IntT i] else []
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


and var_kind_atom (kind:kind_t) (a:atom) : term list =
  match a with
    Append(p1,p2,pres)         -> (var_kind_path kind p1) @
                                  (var_kind_path kind p2) @
                                  (var_kind_path kind pres)
  | Reach(h,add_from,add_to,p) -> (var_kind_mem kind h) @
                                  (var_kind_addr kind add_from) @
                                  (var_kind_addr kind add_to) @
                                  (var_kind_path kind p)
  | ReachAt(h,a_from,a_to,l,p) -> (var_kind_mem kind h) @
                                  (var_kind_addr kind a_from) @
                                  (var_kind_addr kind a_to) @
                                  (var_kind_int kind l) @
                                  (var_kind_path kind p)
  | OrderList(h,a_from,a_to)   -> (var_kind_mem kind h) @
                                  (var_kind_addr kind a_from) @
                                  (var_kind_addr kind a_to)
  | Skiplist(h,s,l,a_from,a_to)-> (var_kind_mem kind h) @
                                  (var_kind_set kind s) @
                                  (var_kind_int kind l) @
                                  (var_kind_addr kind a_from) @
                                  (var_kind_addr kind a_to)
  | In(a,s)                    -> (var_kind_addr kind a) @ (var_kind_set kind s)
  | SubsetEq(s_in,s_out)       -> (var_kind_set kind s_in) @
                                  (var_kind_set kind s_out)
  | InTh(th,s)                 -> (var_kind_tid kind th) @
                                  (var_kind_setth kind s)
  | SubsetEqTh(s_in,s_out)     -> (var_kind_setth kind s_in) @
                                  (var_kind_setth kind s_out)
  | InInt(i,s)                 -> (var_kind_int kind i) @
                                  (var_kind_setint kind s)
  | SubsetEqInt(s_in,s_out)    -> (var_kind_setint kind s_in) @
                                  (var_kind_setint kind s_out)
  | InElem(e,s)                -> (var_kind_elem kind e) @
                                  (var_kind_setelem kind s)
  | SubsetEqElem(s_in,s_out)   -> (var_kind_setelem kind s_in) @
                                  (var_kind_setelem kind s_out)
  | Less(i1,i2)                -> (var_kind_int kind i1) @
                                  (var_kind_int kind i2)
  | Greater(i1,i2)             -> (var_kind_int kind i1) @
                                  (var_kind_int kind i2)
  | LessEq(i1,i2)              -> (var_kind_int kind i1) @
                                  (var_kind_int kind i2)
  | GreaterEq(i1,i2)           -> (var_kind_int kind i1) @
                                  (var_kind_int kind i2)
  | LessTid(t1,t2)             -> (var_kind_tid kind t1) @
                                  (var_kind_tid kind t2)
  | LessElem(e1,e2)            -> (var_kind_elem kind e1) @
                                  (var_kind_elem kind e2)
  | GreaterElem(e1,e2)         -> (var_kind_elem kind e1) @
                                  (var_kind_elem kind e2)
  | Eq(exp)                    -> (var_kind_eq kind exp)
  | InEq(exp)                  -> (var_kind_ineq kind exp)
  | BoolVar v                  -> if (var_k v) = kind then
                                    [VarT v]
                                  else
                                    []
  | BoolArrayRd(arr,t)         -> (var_kind_array kind arr)
  | PC (pc,t,_)                -> []
  | PCUpdate (_,_)             -> []
  | PCRange (pc1,pc2,t,_)      -> []


and var_kind_eq (kind:kind_t) ((t1,t2):eq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)


and var_kind_ineq (kind:kind_t) ((t1,t2):diseq) : term list =
  (var_kind_term kind t1) @ (var_kind_term kind t2)


and var_kind_literal (kind:kind_t) (l:literal) : term list =
  match l with
    Atom a    -> var_kind_atom kind a
  | NegAtom a -> var_kind_atom kind a


and var_kind_conjunctive_formula (kind:kind_t)
                                 (cf:conjunctive_formula) : term list =
  match cf with
    FalseConj -> []
  | TrueConj  -> []
  | Conj ls   -> List.fold_left (fun xs l -> (var_kind_literal kind l)@xs) [] ls


and var_kind_formula (kind:kind_t) (phi:formula) : term list =
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


let var_kind (kind:kind_t) (e:expr_t) : term list =
  let ghost_list = var_kind_expr kind e in
  let ghost_set = List.fold_left (fun set e -> TermSet.add e set)
                               (TermSet.empty)
                               (ghost_list)
  in
    TermSet.elements ghost_set




(* PARAMETRIZATION FUNCTIONS *)

let rec param_a_term (pfun:variable option -> tid option) (expr:term) : term =
  match expr with
    VarT(v)           -> VarT       (set_var_th v (pfun (Some v)))
  | SetT(set)         -> SetT       (param_set      pfun set    )
  | AddrT(addr)       -> AddrT      (param_addr_aux pfun addr   )
  | ElemT(elem)       -> ElemT      (param_elem_aux pfun elem   )
  | ThidT(th)         -> ThidT      (param_tid_aux  pfun th     )
  | CellT(cell)       -> CellT      (param_cell_aux pfun cell   )
  | SetThT(setth)     -> SetThT     (param_setth    pfun setth  )
  | SetIntT(setint)   -> SetIntT    (param_setint   pfun setint )
  | SetElemT(setelem) -> SetElemT   (param_setelem  pfun setelem)
  | PathT(path)       -> PathT      (param_path     pfun path   )
  | MemT(mem)         -> MemT       (param_mem      pfun mem    )
  | IntT(i)           -> IntT       (param_int_aux      pfun i      )
  | ArrayT(arr)       -> ArrayT     (param_arrays   pfun arr    )
  | AddrArrayT(arr)   -> AddrArrayT (param_addrarr  pfun arr    )
  | TidArrayT(arr)    -> TidArrayT  (param_tidarr   pfun arr    )


and param_expr_aux (pfun:variable option -> tid option) (expr:expr_t): expr_t =
  match expr with
    Term t    -> Term (param_a_term pfun t)
  | Formula b -> Formula (param_formula pfun b)


and param_arrays (pfun:variable option -> tid option) (arr:arrays) : arrays =
  match arr with
    VarArray v       -> VarArray (set_var_th v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | ArrayUp(arr,t,e) -> ArrayUp(param_arrays pfun arr, t,
                                param_expr_aux pfun e)


and param_addrarr (pfun:variable option -> tid option) (arr:addrarr) : addrarr =
  match arr with
    VarAddrArray v       -> VarAddrArray (set_var_th v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(param_addrarr pfun arr,
                                        param_int_aux pfun i,
                                        param_addr_aux pfun a)
  | CellArr c            -> CellArr (param_cell_aux pfun c)


and param_tidarr (pfun:variable option -> tid option) (arr:tidarr) : tidarr =
  match arr with
    VarTidArray v       -> VarTidArray (set_var_th v (pfun (Some v)))
      (*TODO: Fix open array case for array variables *)
  | TidArrayUp(arr,i,t) -> TidArrayUp(param_tidarr pfun arr,
                                      param_int_aux pfun i,
                                      param_tid_aux pfun t)
  | CellTids c            -> CellTids (param_cell_aux pfun c)


and param_set (pfun:variable option -> tid option) (e:set) : set =
  match e with
    VarSet v             -> VarSet (set_var_th v (pfun (Some v)))
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


and param_addr_aux (pfun:variable option -> tid option) (a:addr) : addr =
  match a with
    VarAddr v                 -> VarAddr (set_var_th v (pfun (Some v)))
  | Null                      -> Null
  | Next(cell)                -> Next(param_cell_aux pfun cell)
  | NextAt(cell,l)            -> NextAt(param_cell_aux pfun cell,
                                        param_int_aux pfun l)
  | FirstLocked(mem,path)     -> FirstLocked(param_mem pfun mem,
                                             param_path pfun path)
  | FirstLockedAt(mem,path,l) -> FirstLockedAt(param_mem pfun mem,
                                               param_path pfun path,
                                               param_int_aux pfun l)
  | AddrArrayRd(arr,t)        -> AddrArrayRd(param_arrays pfun arr, t)
  | AddrArrRd(arr,l)          -> AddrArrRd(param_addrarr pfun arr,
                                           param_int_aux pfun l)


and param_elem_aux (pfun:variable option -> tid option) (e:elem) : elem =
  match e with
    VarElem v            -> VarElem (set_var_th v (pfun (Some v)))
  | CellData(cell)       -> CellData(param_cell_aux pfun cell)
  | ElemArrayRd(arr,t)   -> ElemArrayRd(param_arrays pfun arr, t)
  | HavocListElem        -> HavocListElem
  | HavocSkiplistElem    -> HavocSkiplistElem
  | LowestElem           -> LowestElem
  | HighestElem          -> HighestElem


and param_tid_aux (pfun:variable option -> tid option) (th:tid) : tid =
  match th with
    VarTh v              -> VarTh (set_var_th v (pfun (Some v)))
  | NoThid               -> NoThid
  | CellLockId(cell)     -> CellLockId(param_cell_aux pfun cell)
  | CellLockIdAt(cell,l) -> CellLockIdAt(param_cell_aux pfun cell,
                                         param_int_aux pfun l)
  | ThidArrayRd(arr,t)   -> ThidArrayRd(param_arrays pfun arr, t)
  | ThidArrRd(arr,l)     -> ThidArrRd(param_tidarr pfun arr,
                                      param_int_aux pfun l)


and param_cell_aux (pfun:variable option -> tid option) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (set_var_th v (pfun (Some v)))
  | Error                  -> Error
  | MkCell(data,addr,th)   -> MkCell(param_elem_aux pfun data,
                                   param_addr_aux pfun addr,
                                   param_tid_aux pfun th)
  | MkSLKCell(data,aa,tt)  -> MkSLKCell(param_elem_aux pfun data,
                                        List.map (param_addr_aux pfun) aa,
                                        List.map (param_tid_aux pfun) tt)
  | MkSLCell(data,aa,ta,l) -> MkSLCell(param_elem_aux pfun data,
                                       param_addrarr pfun aa,
                                       param_tidarr pfun ta,
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


and param_setth (pfun:variable option -> tid option) (s:setth) : setth =
  match s with
    VarSetTh v            -> VarSetTh (set_var_th v (pfun (Some v)))
  | EmptySetTh            -> EmptySetTh
  | SinglTh(th)           -> SinglTh(param_tid_aux pfun th)
  | UnionTh(s1,s2)        -> UnionTh(param_setth pfun s1,
                                     param_setth pfun s2)
  | IntrTh(s1,s2)         -> IntrTh(param_setth pfun s1,
                                    param_setth pfun s2)
  | SetdiffTh(s1,s2)      -> SetdiffTh(param_setth pfun s1,
                                       param_setth pfun s2)
  | SetThArrayRd(arr,t)   -> SetThArrayRd(param_arrays pfun arr, t)


and param_setint (pfun:variable option -> tid option) (s:setint) : setint =
  match s with
    VarSetInt v            -> VarSetInt (set_var_th v (pfun (Some v)))
  | EmptySetInt            -> EmptySetInt
  | SinglInt(i)            -> SinglInt(param_int_aux pfun i)
  | UnionInt(s1,s2)        -> UnionInt(param_setint pfun s1,
                                       param_setint pfun s2)
  | IntrInt(s1,s2)         -> IntrInt(param_setint pfun s1,
                                    param_setint pfun s2)
  | SetdiffInt(s1,s2)      -> SetdiffInt(param_setint pfun s1,
                                       param_setint pfun s2)
  | SetIntArrayRd(arr,t)   -> SetIntArrayRd(param_arrays pfun arr, t)


and param_setelem (pfun:variable option -> tid option) (s:setelem) : setelem =
  match s with
    VarSetElem v            -> VarSetElem (set_var_th v (pfun (Some v)))
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


and param_path (pfun:variable option -> tid option) (path:path) : path =
  match path with
    VarPath v                        -> VarPath (set_var_th v (pfun (Some v)))
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


and param_mem (pfun:variable option -> tid option) (m:mem) : mem =
  match m with
    VarMem v             -> VarMem (set_var_th v (pfun (Some v)))
  | Update(mem,add,cell) -> Update(param_mem pfun mem,
                                   param_addr_aux pfun add,
                                   param_cell_aux pfun cell)
  | MemArrayRd(arr,t)    -> MemArrayRd(param_arrays pfun arr, t)


and param_int_aux (pfun:variable option -> tid option) (i:integer) : integer =
  match i with
    IntVal(i)           -> IntVal(i)
  | VarInt v            -> VarInt (set_var_th v (pfun (Some v)))
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


and param_atom (pfun:variable option -> tid option) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)         -> Append(param_path pfun p1,
                                         param_path pfun p2,
                                         param_path pfun pres)
  | Reach(h,add_from,add_to,p) -> Reach(param_mem pfun h,
                                        param_addr_aux pfun add_from,
                                        param_addr_aux pfun add_to,
                                        param_path pfun p)
  | ReachAt(h,a_from,a_to,l,p) -> ReachAt(param_mem pfun h,
                                          param_addr_aux pfun a_from,
                                          param_addr_aux pfun a_to,
                                          param_int_aux pfun l,
                                          param_path pfun p)
  | OrderList(h,a_from,a_to)   -> OrderList(param_mem pfun h,
                                            param_addr_aux pfun a_from,
                                            param_addr_aux pfun a_to)
  | Skiplist(h,s,l,a_from,a_to)-> Skiplist(param_mem pfun h,
                                           param_set pfun s,
                                           param_int_aux pfun l,
                                           param_addr_aux pfun a_from,
                                           param_addr_aux pfun a_to)
  | In(a,s)                    -> In(param_addr_aux pfun a,
                                     param_set pfun s)
  | SubsetEq(s_in,s_out)       -> SubsetEq(param_set pfun s_in,
                                           param_set pfun s_out)
  | InTh(th,s)                 -> InTh(param_tid_aux pfun th,
                                       param_setth pfun s)
  | SubsetEqTh(s_in,s_out)     -> SubsetEqTh(param_setth pfun s_in,
                                             param_setth pfun s_out)
  | InInt(i,s)                 -> InInt(param_int_aux pfun i,
                                        param_setint pfun s)
  | SubsetEqInt(s_in,s_out)    -> SubsetEqInt(param_setint pfun s_in,
                                              param_setint pfun s_out)
  | InElem(e,s)                -> InElem(param_elem_aux pfun e,
                                         param_setelem pfun s)
  | SubsetEqElem(s_in,s_out)   -> SubsetEqElem(param_setelem pfun s_in,
                                               param_setelem pfun s_out)
  | Less(i1,i2)                -> Less(param_int_aux pfun i1,
                                       param_int_aux pfun i2)
  | Greater(i1,i2)             -> Greater(param_int_aux pfun i1,
                                          param_int_aux pfun i2)
  | LessEq(i1,i2)              -> LessEq(param_int_aux pfun i1,
                                         param_int_aux pfun i2)
  | GreaterEq(i1,i2)           -> GreaterEq(param_int_aux pfun i1,
                                            param_int_aux pfun i2)
  | LessTid(t1,t2)             -> LessTid(param_tid_aux pfun t1,
                                          param_tid_aux pfun t2)
  | LessElem(e1,e2)            -> LessElem(param_elem_aux pfun e1,
                                           param_elem_aux pfun e2)
  | GreaterElem(e1,e2)         -> GreaterElem(param_elem_aux pfun e1,
                                              param_elem_aux pfun e2)
  | Eq(exp)                    -> Eq(param_eq pfun exp)
  | InEq(exp)                  -> InEq(param_ineq pfun exp)
  | BoolVar v                  -> BoolVar (set_var_th v (pfun (Some v)))
  | BoolArrayRd(arr,t)         -> BoolArrayRd(param_arrays pfun arr, t)
      (* TODO: Fix, not sure if for open arrays is correct *)
  | PC (pc,_,p)                -> PC (pc, pfun None, p)
  | PCUpdate (pc,t)            -> PCUpdate (pc,t)
  | PCRange (pc1,pc2,_,p)      -> PCRange (pc1, pc2, pfun None, p)


and param_literal (pfun:variable option -> tid option) (l:literal) : literal =
  match l with
    Atom a    -> Atom    (param_atom pfun a)
  | NegAtom a -> NegAtom (param_atom pfun a)


and param_eq (pfun:variable option -> tid option) ((t1,t2):eq) : eq =
  (param_a_term pfun t1, param_a_term pfun t2)


and param_ineq (pfun:variable option -> tid option) ((t1,t2):diseq) : diseq =
  (param_a_term pfun t1, param_a_term pfun t2)

    
and param_conjunctive_formula (pfun:variable option -> tid option)
                              (cf:conjunctive_formula) : conjunctive_formula =
  match cf with
    FalseConj -> FalseConj
  | TrueConj  -> TrueConj
  | Conj ls   -> Conj (List.map (param_literal pfun) ls)


and param_formula (pfun:variable option -> tid option) (phi:formula) : formula =
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


let param_local_only (th_p:tid option) (v_opt:variable option) : tid option =
  match v_opt with
    None -> th_p
  | Some v -> if is_local_var v then th_p else None


let param (th_p:tid option) (f:formula) : formula =
  param_formula (param_local_only th_p) f


let param_term (th_p:tid option) (t:term) : term =
  param_a_term (param_local_only th_p) t


let param_expr (th_p:tid option) (e:expr_t) : expr_t =
  param_expr_aux (param_local_only th_p) e


let param_cell (th_p:tid option) (c:cell) : cell =
  param_cell_aux (param_local_only th_p) c


let param_elem (th_p:tid option) (e:elem) : elem =
  param_elem_aux (param_local_only th_p) e


let param_addr (th_p:tid option) (a:addr) : addr =
  param_addr_aux (param_local_only th_p) a


let param_th (th_p:tid option) (t:tid) : tid =
  param_tid_aux (param_local_only th_p) t


let param_int (th_p:tid option) (i:integer) : integer =
  param_int_aux (param_local_only th_p) i


let param_variable (th_p:tid option) (v:variable) : variable =
    set_var_th v (param_local_only th_p (Some v))


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


let subst_domain_in (tid_list:tid list) (subst:tid_subst_t) : bool =
  List.for_all (fun (d,_) -> List.mem d tid_list) subst


let subst_codomain_in (tid_list:tid list) (subst:tid_subst_t) : bool =
  List.for_all (fun (_,r) -> List.mem r tid_list) subst


let subst_full_assign (tid_list:tid list) (subst:tid_subst_t) : bool =
  let dom = subst_domain subst
  in
    List.for_all (fun t -> ThreadSet.mem t dom) tid_list
    

let rec subst_tid_term (subs:tid_subst_t) (expr:term) : term =
  match expr with
    VarT v              -> VarT (set_var_th v
                                 (Option.lift (subst_tid_th subs) (var_th v)))
  | SetT(set)           -> SetT(subst_tid_set subs set)
  | AddrT(addr)         -> AddrT(subst_tid_addr subs addr)
  | ElemT(elem)         -> ElemT(subst_tid_elem subs elem)
  | ThidT(th)           -> ThidT(subst_tid_th subs th)
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
    VarArray v       -> VarArray (set_var_th v
                                    (Option.lift(subst_tid_th subs) (var_th v)))
  | ArrayUp(arr,t,e) -> ArrayUp(subst_tid_array subs arr, t,
                                subst_tid_expr subs e)


and subst_tid_addrarr (subs:tid_subst_t) (expr:addrarr) : addrarr =
  match expr with
    VarAddrArray v       -> VarAddrArray (set_var_th v
                                    (Option.lift(subst_tid_th subs) (var_th v)))
  | AddrArrayUp(arr,i,a) -> AddrArrayUp(subst_tid_addrarr subs arr,
                                        subst_tid_int subs i,
                                        subst_tid_addr subs a)
  | CellArr c            -> CellArr(subst_tid_cell subs c)


and subst_tid_tidarr (subs:tid_subst_t) (expr:tidarr) : tidarr =
  match expr with
    VarTidArray v       -> VarTidArray (set_var_th v
                                    (Option.lift(subst_tid_th subs) (var_th v)))
  | TidArrayUp(arr,i,t) -> TidArrayUp(subst_tid_tidarr subs arr,
                                      subst_tid_int subs i,
                                      subst_tid_th subs t)
  | CellTids c            -> CellTids (subst_tid_cell subs c)


and subst_tid_set (subs:tid_subst_t) (e:set) : set =
  match e with
    VarSet v            -> VarSet (set_var_th v
                                  (Option.lift (subst_tid_th subs) (var_th v)))
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
    VarAddr v                 -> VarAddr(set_var_th v
                                  (Option.lift(subst_tid_th subs) (var_th v)))
  | Null                      -> Null
  | Next(cell)                -> Next(subst_tid_cell subs cell)
  | NextAt(cell,l)            -> NextAt(subst_tid_cell subs cell,
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
    VarElem v             -> VarElem(set_var_th v
                                (Option.lift (subst_tid_th subs) (var_th v)))
  | CellData(cell)        -> CellData(subst_tid_cell subs cell)
  | ElemArrayRd(arr,t)    -> ElemArrayRd(subst_tid_array subs arr, t)
  | HavocListElem         -> HavocListElem
  | HavocSkiplistElem     -> HavocSkiplistElem
  | LowestElem            -> LowestElem
  | HighestElem           -> HighestElem


(*
and subst_tid_th (subs:tid_subst_t) (th:tid) : tid =
  match th with
(* FIX: Not sure if this is OK.
    I am substituting a global tid. Local tids replace only its parameter
*)
    VarTh v -> if var_proc v <> None then
                 VarTh (set_var_th v (Option.lift (subst_tid_th subs)))
               else
                 let curr_th = build_var_tid id in
                 let new_th = subst_tid_th subs curr_th
                 in
                   begin
                     match new_th with
                       VarTh v' -> set_var_id v (var_id v')
                     | NoThid   -> NoThid
                     | CellLockId c -> CellLockId c
                     | ThidArrayRd (a,t) -> ThidArrayRd (a,t)
                   end
  | NoThid              -> NoThid
  | CellLockId(cell)    -> CellLockId(subst_tid_cell subs cell)
  | ThidArrayRd(arr,t)  -> ThidArrayRd(subst_tid_array subs arr, t)
*)

and subst_tid_cell (subs:tid_subst_t) (c:cell) : cell =
  match c with
    VarCell v              -> VarCell (set_var_th v
                                (Option.lift (subst_tid_th subs) (var_th v)))
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


and subst_tid_setth (subs:tid_subst_t) (s:setth) : setth =
  match s with
    VarSetTh v             -> VarSetTh(set_var_th v
                                (Option.lift (subst_tid_th subs) (var_th v)))
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
    VarSetInt v             -> VarSetInt(set_var_th v
                                  (Option.lift (subst_tid_th subs) (var_th v)))
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
    VarSetElem v             -> VarSetElem(set_var_th v
                                (Option.lift (subst_tid_th subs) (var_th v)))
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
    VarPath v                        -> VarPath(set_var_th v
                                          (Option.lift (subst_tid_th subs) (var_th v)))
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
    VarMem v             -> VarMem(set_var_th v
                                  (Option.lift (subst_tid_th subs) (var_th v)))
  | Update(mem,add,cell) -> Update(subst_tid_mem subs mem,
                                   subst_tid_addr subs add,
                                   subst_tid_cell subs cell)
  | MemArrayRd(arr,t)   -> MemArrayRd(subst_tid_array subs arr, t)


and subst_tid_int (subs:tid_subst_t) (i:integer) : integer =
  match i with
    IntVal(i)         -> IntVal(i)
  | VarInt v          -> VarInt(set_var_th v
                                (Option.lift (subst_tid_th subs) (var_th v)))
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
              | NoThid -> t
              | CellLockId c -> CellLockId (subst_tid_cell subs c)
              | CellLockIdAt (c,l) -> CellLockIdAt (subst_tid_cell subs c,
                                                    subst_tid_int subs l)
              | ThidArrayRd (a,p) -> ThidArrayRd (subst_tid_array subs a,
                                                  subst_tid_th subs p)
              | ThidArrRd (a,i) -> ThidArrRd (subst_tid_tidarr subs a,
                                              subst_tid_int subs i)
            end


and subst_tid_atom (subs:tid_subst_t) (a:atom) : atom =
  match a with
    Append(p1,p2,pres)         -> Append(subst_tid_path subs p1,
                                         subst_tid_path subs p2,
                                         subst_tid_path subs pres)
  | Reach(h,add_from,add_to,p) -> Reach(subst_tid_mem subs h,
                                        subst_tid_addr subs add_from,
                                        subst_tid_addr subs add_to,
                                        subst_tid_path subs p)
  | ReachAt(h,a_from,a_to,l,p) -> ReachAt(subst_tid_mem subs h,
                                          subst_tid_addr subs a_from,
                                          subst_tid_addr subs a_to,
                                          subst_tid_int subs l,
                                          subst_tid_path subs p)
  | OrderList(h,a_from,a_to)   -> OrderList(subst_tid_mem subs h,
                                            subst_tid_addr subs a_from,
                                            subst_tid_addr subs a_to)
  | Skiplist(h,s,l,a_from,a_to)-> Skiplist(subst_tid_mem subs h,
                                           subst_tid_set subs s,
                                           subst_tid_int subs l,
                                           subst_tid_addr subs a_from,
                                           subst_tid_addr subs a_to)
  | In(a,s)                    -> In(subst_tid_addr subs a,
                                     subst_tid_set subs s)
  | SubsetEq(s_in,s_out)       -> SubsetEq(subst_tid_set subs s_in,
                                           subst_tid_set subs s_out)
  | InTh(th,s)                 -> InTh(subst_tid_th subs th,
                                       subst_tid_setth subs s)
  | SubsetEqTh(s_in,s_out)     -> SubsetEqTh(subst_tid_setth subs s_in,
                                             subst_tid_setth subs s_out)
  | InInt(i,s)                 -> InInt(subst_tid_int subs i,
                                        subst_tid_setint subs s)
  | SubsetEqInt(s_in,s_out)    -> SubsetEqInt(subst_tid_setint subs s_in,
                                              subst_tid_setint subs s_out)
  | InElem(e,s)                -> InElem(subst_tid_elem subs e,
                                         subst_tid_setelem subs s)
  | SubsetEqElem(s_in,s_out)   -> SubsetEqElem(subst_tid_setelem subs s_in,
                                               subst_tid_setelem subs s_out)
  | Less(i1,i2)                -> Less(subst_tid_int subs i1,
                                       subst_tid_int subs i2)
  | Greater(i1,i2)             -> Greater(subst_tid_int subs i1,
                                          subst_tid_int subs i2)
  | LessEq(i1,i2)              -> LessEq(subst_tid_int subs i1,
                                         subst_tid_int subs i2)
  | GreaterEq(i1,i2)           -> GreaterEq(subst_tid_int subs i1,
                                            subst_tid_int subs i2)
  | LessTid(t1,t2)             -> LessTid(subst_tid_th subs t1,
                                          subst_tid_th subs t2)
  | LessElem(e1,e2)            -> LessElem(subst_tid_elem subs e1,
                                           subst_tid_elem subs e2)
  | GreaterElem(e1,e2)         -> GreaterElem(subst_tid_elem subs e1,
                                              subst_tid_elem subs e2)
  | Eq(exp)                    -> Eq(subst_tid_eq subs exp)
  | InEq(exp)                  -> InEq(subst_tid_ineq subs exp)
  | BoolVar v                  -> BoolVar(set_var_th v
                                  (Option.lift (subst_tid_th subs) (var_th v)))
  | BoolArrayRd(arr,t)         -> BoolArrayRd(subst_tid_array subs arr, t)
  | PC (pc,t,primed)           -> PC (pc, Option.lift(subst_tid_th subs) t,
                                      primed)
  | PCUpdate (pc,t)            -> PCUpdate (pc, subst_tid_th subs t)
  | PCRange (pc1,pc2,t,primed) -> PCRange (pc1, pc2, Option.lift(subst_tid_th subs) t,
                                            primed)


and subst_tid_literal (subs:tid_subst_t) (l:literal) : literal =
  match l with
    Atom a    -> Atom (subst_tid_atom subs a)
  | NegAtom a -> NegAtom (subst_tid_atom subs a)


and subst_tid_eq (subs:tid_subst_t) ((t1,t2):eq) : eq =
  (subst_tid_term subs t1, subst_tid_term subs t2)


and subst_tid_ineq (subs:tid_subst_t) ((t1,t2):diseq) : diseq =
  (subst_tid_term subs t1, subst_tid_term subs t2)


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


let subst_to_str (sub:tid_subst_t) : string =
  "{" ^ (String.concat ", " $
         List.map (fun (i,j) -> (tid_to_str j)^"<-"^(tid_to_str i)) sub) ^ "}"


(* FORMULA MANIPULATION FUNCTIONS *)
let conj_list (bs:formula list) : formula =
  match bs with
    [] -> True
  | x::xs -> List.fold_left (fun a b -> And(a,b)) x xs

  
let disj_list (bs:formula list) : formula =
  match bs with
    [] -> False
  | x::xs -> List.fold_left (fun a b -> Or(a,b)) x xs


let conj_literals (ls:literal list) :  formula =
  match ls with
      []    -> True
    | x::xs -> List.fold_left (fun phi l -> And(phi,Literal l)) (Literal x) xs  

let disj_literals  (ls:literal list) : formula =
  match ls with
      []    -> False
    | x::xs -> List.fold_left (fun phi l -> Or(phi,Literal l)) (Literal x) xs 


let rec to_conj_list (phi:formula) : formula list =
  match phi with
    And (f1,f2) -> (to_conj_list f1) @ (to_conj_list f2)
  | _           -> [phi]


let rec to_disj_list (phi:formula) : formula list =
  match phi with
    Or (f1,f2) -> (to_disj_list f1) @ (to_disj_list f2)
  | _          -> [phi]


let rec dnf_count (expr:formula) : (float * float) =
  match expr with
    Iff (e1,e2) -> dnf_count (And (Implies (e1,e2),Implies (e2,e1)))
  | Implies(e1,e2) -> dnf_count (Or (Not e1, e2))
  | And(e1,e2)  -> let (l1, max1) = dnf_count e1 in
                   let (l2, max2) = dnf_count e2 in
                     (l1*.l2, max max1 max2)
  | Or(e1,e2)   -> let (l1, max1) = dnf_count e1 in
                   let (l2, max2) = dnf_count e2 in
                     (l1+.l2, max max1 max2)
  | Not (Not e) -> dnf_count e
  | Not (And (e1,e2)) -> dnf_count (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> dnf_count (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> dnf_count (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> dnf_count (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> (1.0,1.0)


let rec dnf (expr:formula) : formula list list =
  match expr with
    Iff (e1,e2) -> dnf (And (Implies (e1,e2),Implies (e2,e1)))
  | Implies(e1,e2) -> dnf (Or (Not e1, e2))
  | And(e1,e2)  -> let e1_dnf = dnf e1 in
                   let e2_dnf = dnf e2 in
                     List.fold_left (fun final_lst x1 ->
                       let lst = List.fold_left (fun l2 x2 ->
(*                                  And(x1,x2) :: l2 *)
                                    (x1 @ x2) :: l2
                                 ) [] e2_dnf
                       in
                          lst @ final_lst
                     ) [] e1_dnf
  | Or(e1,e2)   -> dnf e1 @ dnf e2
  | Not (Not e) -> dnf e
  | Not (And (e1,e2)) -> dnf (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> dnf (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> dnf (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> dnf (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> [[e]]


let rec cnf (expr:formula) : formula list list =
  match expr with
    Iff (e1,e2) -> cnf (And (Implies (e1,e2),Implies (e2,e1)))
  | Implies(e1,e2) -> cnf (Or (Not e1, e2))
  | Or(e1,e2)   -> let e1_cnf = cnf e1 in
                   let e2_cnf = cnf e2 in
                     List.fold_left (fun final_lst x1 ->
                       let lst = List.fold_left (fun l2 x2 ->
                                    (x1 @ x2) :: l2
                                 ) [] e2_cnf
                       in
                          lst @ final_lst
                     ) [] e1_cnf
  | And (e1,e2) -> cnf e1 @ cnf e2
  | Not (Not e) -> cnf e
  | Not (And (e1,e2)) -> cnf (Or (Not e1, Not e2))
  | Not (Or (e1, e2)) -> cnf (And (Not e1, Not e2))
  | Not (Implies (e1, e2)) -> cnf (And (e1, Not e2))
  | Not (Iff (e1, e2)) -> cnf (Or (And (e1, Not e2), And (Not e1, e2)))
  | e -> [[e]]


(* Converts an expression to a format understandable by Sriram's tool "trs" *)
let rec to_trs (expr:formula) : formula =
  let add_one i = IntAdd (i, IntVal 1) in
  let tid_to_int t = match t with
                       VarTh v -> VarInt v
                     | _ -> let msg = "Tid to int conversion in to_trs" in
                              RAISE(Not_implemented msg) in
  let rec conv e neg =
    (* First argument in formula, second tells if it must be negated *)
    match (e,neg) with
      (True, false)   -> True
    | (True, true)    -> False
    | (False, false)  -> False
    | (False, true)   -> True
    | (Literal (NegAtom a), false) -> conv (Literal (Atom a)) true
    | (Literal (NegAtom a), true ) -> conv (Literal (Atom a)) false
    | (Literal (Atom (Less (n,m))),            false) -> Literal (Atom (LessEq    (add_one n,m)))
    | (Literal (Atom (Less (n,m))),            true ) -> Literal (Atom (GreaterEq (n,m)))
    | (Literal (Atom (Greater (n,m))),         false) -> Literal (Atom (GreaterEq (n,add_one m)))
    | (Literal (Atom (Greater (n,m))),         true ) -> Literal (Atom (LessEq    (n,m)))
    | (Literal (Atom (LessEq (n,m))),          false) -> Literal (Atom (LessEq    (n,m)))
    | (Literal (Atom (LessEq (n,m))),          true ) -> Literal (Atom (GreaterEq (n,add_one m)))
    | (Literal (Atom (GreaterEq (n,m))),       false) -> Literal (Atom (GreaterEq (n,m)))
    | (Literal (Atom (GreaterEq (n,m))),       true ) -> Literal (Atom (LessEq    (add_one n,m)))
    | (Literal (Atom (Eq (IntT n, IntT m))),   false) -> Literal (Atom (Eq        (IntT n, IntT m)))
    | (Literal (Atom (Eq (IntT n, IntT m))),   true ) -> Or (Literal (Atom (LessEq   (add_one n,m))),
                                                             Literal (Atom (GreaterEq(n,add_one m))))
    | (Literal (Atom (InEq (IntT n, IntT m))), false) -> Or (Literal (Atom (LessEq   (add_one n,m))),
                                                             Literal (Atom (GreaterEq(n,add_one m))))
    | (Literal (Atom (InEq (IntT n, IntT m))), true ) -> Literal (Atom (Eq (IntT n, IntT m)))
    | (Literal (Atom (LessTid (s,t))),         false) -> Literal (Atom (LessEq (add_one (tid_to_int s),
                                                                                         tid_to_int t)))
    | (Literal (Atom (LessTid (s,t))),         true ) -> Literal (Atom (GreaterEq (tid_to_int s,
                                                                                   tid_to_int t)))
    | (And (e1, e2),     false) -> And (conv e1 false, conv e2 false)
    | (And (e1, e2),     true ) -> Or (conv e1 true, conv e2 true)
    | (Or (e1, e2),      false) -> Or (conv e1 false, conv e2 false)
    | (Or (e1, e2),      true ) -> And (conv e1 true, conv e2 true)
    | (Not e,            false) -> conv e true
    | (Not e,            true ) -> conv e false
    | (Implies (e1, e2), false) -> Or (conv e1 true, conv e2 false)
    | (Implies (e1, e2), true ) -> And (conv e1 false, conv e2 true)
    | (Iff (e1, e2),     false) -> And (Or (conv e1 true, conv e2 false),
                                        Or (conv e1 false, conv e2 true))
    | (Iff (e1, e2),     true ) -> Or (And (conv e1 false, conv e2 true),
                                      And (conv e1 true, conv e2 false))
    | (e,                false) -> e
    | (e,                true ) -> Not e
  in
    conv expr false

 


(* INITIAL ASSIGNMENT FUNCTION *)
let assign_var (p_name:string option)
               (v:varId)
               (info:var_info_t) : formula list =
  let e  = var_info_expr info in
    match e with
      Some (Equality t)  -> let new_var = convert_var_to_term p_name v info in
                              [Literal (Atom (Eq (new_var, t)))]
    | Some (Condition c) -> [c]
    | None               -> []



(* EXPRESSION PRESERVATION FUNCTIONS *)
let pres_th_param (t:term) (new_th:tid option) : tid option =
  let owner = get_var_owner t in
  match owner with
    Some _ -> new_th
  | None   -> None


let construct_term_eq (v:term)
                      (th_p:tid option)
                      (e:expr_t) : (term list * formula) =
(*  let new_th = pres_th_param v th_p in *)

  match (v,e) with
    (* Variables *)
    (VarT var, Formula t) ->
      (* Possibly I have to inject the Bool sort to the variable *)
      let modif     = [VarT (var_base_info var)] in
      let new_th    = pres_th_param v th_p in
      let left_atom = prime_atom (BoolVar (set_var_th var new_th)) in
      let param_t   = param th_p t
      in
        (modif, Iff (Literal (Atom left_atom), param_t))

  | (VarT var, Term t) ->
      let modif     = [VarT (var_base_info var)] in
      let new_th    = pres_th_param v th_p in
      let left_term = prime_term $ param_term new_th v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Sets of addresses *)
  | (SetT (VarSet var), Term t) ->
      let modif     = [SetT(VarSet(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Sets of integers *)
  | (SetIntT (VarSetInt var), Term t) ->
      let modif     = [SetIntT(VarSetInt(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Sets of elements *)
  | (SetElemT (VarSetElem var), Term t) ->
      let modif     = [SetElemT(VarSetElem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Sets of threads *)
  | (SetThT (VarSetTh var), Term t) ->
      let modif     = [SetThT(VarSetTh(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Elements *)
  | (ElemT (VarElem var), Term t) ->
      let modif     = [ElemT(VarElem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (ElemT (CellData (VarCell var)), Term t) ->
      let modif     = [ElemT(CellData(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Threads *)
  | (ThidT (VarTh var), Term t) ->
      let modif     = [ThidT(VarTh(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (ThidT (CellLockId (VarCell var)), Term t) ->
      let modif     = [ThidT (CellLockId(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (ThidT (CellLockIdAt (VarCell var, i)), Term t) ->
      let modif     = [ThidT (CellLockIdAt(VarCell(var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (ThidT (ThidArrRd (CellTids (VarCell var), i)), Term t) ->
      let modif     = [ThidT (ThidArrRd (CellTids(VarCell(var_base_info var)),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (ThidT (ThidArrRd (VarTidArray var,i)), Term t) ->
      let modif     = [ThidT(ThidArrRd(VarTidArray (var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Addresses *)
  | (AddrT (VarAddr var), Term t) ->
      let modif     = [AddrT(VarAddr(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (AddrT (Next (VarCell var)), Term t) ->
      let modif     = [AddrT(Next(VarCell(var_base_info var)))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (AddrT (NextAt (VarCell var, i)), Term t) ->
      let modif     = [AddrT(NextAt(VarCell(var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (AddrT (AddrArrRd (CellArr (VarCell var), i)), Term t) ->
      let modif     = [AddrT(AddrArrRd(CellArr(VarCell(var_base_info var)),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  | (AddrT (AddrArrRd (VarAddrArray var,i)), Term t) ->
      let modif     = [AddrT(AddrArrRd(VarAddrArray (var_base_info var),i))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Cells *)
  (* TODO: Not sure if this case is ok *)
  | (CellT (VarCell var as c), Term CellT (CellLock (VarCell _, _))) ->
      let new_th    = pres_th_param v th_p in
      let modif     = [ThidT(CellLockId(VarCell(var_base_info var)))] in
      let new_tid   = Option.default NoThid th_p in
      let left_term = prime_term (CellT (VarCell
                        (set_var_th (set_var_pr var false) new_th))) in
      (modif, Literal (Atom (Eq (left_term, CellT(MkCell(CellData c, Next c, new_tid))))))

  (* TOFIX: We are missing the case for TSLK and TSL *)

  | (CellT (VarCell var), Term t) ->
      let modif     = [CellT(VarCell(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))


  (* Paths *)
  | (PathT (VarPath var), Term t) ->
      let modif     = [PathT(VarPath(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Memories *)
  | (MemT (VarMem var), Term t) ->
      let modif     = [MemT(VarMem(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Integers *)
  | (IntT (VarInt var), Term t) ->
      let modif = [IntT(VarInt(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Arrays with domain of thread identifiers *)
  | (ArrayT (VarArray var), Term t) ->
      let modif     = [ArrayT(VarArray(var_base_info var))] in
      let left_term = prime_term $ param_term th_p v in
      let param_t   = param_term th_p t
      in
        (modif, Literal (Atom (Eq (left_term, param_t))))

  (* Pointer support *)
  (* Missing for this cases =( *)
  | (_, Term t)                 ->
      Interface.Err.msg "Unexpected assignment" $
              sprintf "When constructing transition relation for \
                       assignment between term \"%s\" and \
                       expression \"%s\"." (term_to_str v)
                                           (term_to_str t);
      RAISE(Incompatible_assignment(v,e))

  | (_, Formula t)                ->
      Interface.Err.msg "Unexpected assignment" $
              sprintf "When construction transition relation for \
                       assignment between term \"%s\" and formula \
                       expression \"%s\"." (term_to_str v)
                                           (formula_to_str t);
      RAISE(Incompatible_assignment(v,e))


let construct_pres_term (t:term) (th_p:tid option) : formula =
  match t with
    VarT var -> let bool_var = Formula (Literal (Atom (BoolVar var))) in
                  snd $ construct_term_eq t th_p bool_var
  | _        -> snd $ construct_term_eq t th_p (Term (param_term th_p t))



let construct_term_eq_as_array (v:term)
                               (th_p:tid option)
                               (e:expr_t) : (term list * formula) =

  let _ = Printf.printf "CONSTRUCT_TERM_EQ: %s\n" (term_to_str v) in
  let scope = get_var_owner v in
    match (scope, th_p) with
      (Some _, Some th) ->
        begin
          let _ = Printf.printf "CASE A\n" in
          let arr        = array_var_from_term v false in
          let primed_arr = array_var_from_term v true in
          let new_expr   =
            let cell_arr = CellArrayRd(arr,th) in
            match (v,e) with
              (ElemT(CellData(c)), Term (ElemT e)) ->
                Term (CellT (MkCell (param_elem th_p e, Next cell_arr, CellLockId cell_arr)))
            | (AddrT(Next(c)), Term (AddrT a)) ->
                Term (CellT (MkCell (CellData cell_arr, param_addr th_p a, CellLockId cell_arr)))
            | (CellT (VarCell _), Term (CellT(CellLock(d,_)))) ->
                let my_tid = Option.default NoThid th_p in
                let new_d  = param_cell th_p d in
                               Term (CellT (MkCell (CellData new_d, Next new_d, my_tid)))
            | (ThidT(CellLockId(c)), Term (ThidT tid)) ->
                Term (CellT (MkCell (CellData cell_arr, Next cell_arr, param_th th_p tid)))
            | _ -> param_expr th_p e in
          let modif_arr  = ArrayT(ArrayUp(arr, th, new_expr)) in
          let assign     = Literal(Atom(Eq(ArrayT primed_arr, modif_arr))) in
          ([ArrayT arr], assign)
(*
              let modif_arr = Expr.Term (ArrayT(ArrayUp(arr, th, t))) in
              construct_term_eq v None modif_arr
*)
        end
    | (None, _) ->
        begin
          match (v,e) with
          | (AddrT (AddrArrRd(arr,i)), Term (AddrT a)) ->
              let primed_arr = prime_addrarr arr in
              let modif_arr = AddrArrayT(AddrArrayUp(arr, param_int th_p i, param_addr th_p a)) in
              let assign = Literal(Atom(Eq(AddrArrayT primed_arr, modif_arr))) in
              ([AddrArrayT arr], assign)
          | (ThidT (ThidArrRd(arr,i)), Term (ThidT t)) ->
              let primed_arr = prime_tidarr arr in
              let modif_arr = TidArrayT(TidArrayUp(arr, param_int th_p i, param_th th_p t)) in
              let assign = Literal(Atom(Eq(TidArrayT primed_arr, modif_arr))) in
              ([TidArrayT arr], assign)
          | _ -> construct_term_eq v th_p e
        end
(*          (let _ = Printf.printf "CASE B\n" in construct_term_eq v th_p e) *)
    | _ -> Interface.Err.msg "Invalid argument" $
                   sprintf "When trying to construct a local array assignment \
                            for term \"%s\" with expression \"%s\", no thread \
                            identifier to denote the array position to be \
                            modified was provided." (term_to_str v)
                                                    (expr_to_str e);
                   RAISE(Invalid_argument)


(* NUMERIC EXPRESSION FUNCTIONS *)
let new_num_pos_var_id (base:string) (i:int) : varId =
  sprintf "%s%i" base i


let new_label_pos_var_id (base:string) (lbl:string) : varId =
  sprintf "%s%s" base lbl


let new_num_pos_var (base:string) (i:int) : integer =
  VarInt (new_num_pos_var_id base i, Int, false, None, Some "", Normal)


let new_label_pos_var (base:string) (lbl:string) : integer =
  VarInt (new_label_pos_var_id base lbl, Int, false, None, Some "", Normal)


let check_numeric (id:varId) (info:var_info_t) : unit =
  let s = var_info_sort info in
  match s with
    Int  -> ()
  (* We allows tid, provided we interpret them as integer later *)
  | Thid -> ()
  | _   -> Interface.Err.msg "Non-numeric variable" $
             sprintf "Variables are expected to be numeric, but variable \
                      %s has sort %s."
                      (id)
                      (sort_to_str s);
           RAISE(No_numeric_variable(id,s))


(* COUNTING ABSTRACTION FUNCTIONS *)

(* FOR SRIRAM ABS-INT *)
let expr_and_removing_true (f1:formula) (f2:formula) : formula =
  if f1 = True then f2
  else if f2 = True then f1
  else And(f1,f2)


let countAbs_var (i:int) : variable =
  build_var (defCountAbsVar ^ string_of_int i) Int false None None Normal


let someone_at (i:int) : formula =
  let var = new_num_pos_var defCountAbsVar i
  in
    greatereq_form var (IntVal 1)


let someone_at_labels (ls:string list) : formula =
  let loc_vars = List.map (fun l ->
                   let v = new_label_pos_var defCountAbsVar l
                   in
                     greatereq_form v (IntVal 1)
                 ) ls
  in
    conj_list loc_vars


let build_assign (v:integer) (e:integer) : formula =
  eq_int (prime_int v) e


let build_pos_change (curr:int) (next:int) : formula =
  let curr_var    = new_num_pos_var defCountAbsVar curr in
  let next_var    = new_num_pos_var defCountAbsVar next in
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
  let build_label_var lbl = new_label_pos_var defCountAbsVar lbl in
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
    conj_list (only_curr_modif @ only_next_modif @ shared_modif)


let new_formula_info (phi:formula) : formula_info_t =
  {
    formula = phi;
    primed = prime phi;
    voc = voc phi;
    vars = all_vars phi;
  }


let copy_formula_info (info:formula_info_t) : formula_info_t =
  {
    formula = info.formula;
    primed = info.primed;
    voc = info.voc;
    vars = info.vars;
  }


let rec cleanup (phi:formula) : formula =
  match phi with
  | And (e, True)    -> cleanup e
  | And (True, e)    -> cleanup e
  | And (e1, e2)     -> And (cleanup e1, cleanup e2)
  | Or  (e, False)   -> cleanup e
  | Or  (False, e)   -> cleanup e
  | Or (e1, e2)      -> Or (cleanup e1, cleanup e2)
  | Not e            -> Not (cleanup e)
  | Implies (e1, e2) -> Implies(cleanup e1, cleanup e2)
  | Iff (e1, e2)     -> Iff (cleanup e1, cleanup e2)
  | _                -> phi


let cleanup_dup (ps:formula list) : formula list =
  let (_, xs) = List.fold_left (fun (s,xs) p ->
                  let (s',ys') = List.fold_left (fun (s,ys) phi ->
                                   if FormulaSet.mem phi s then
                                     (s,ys)
                                   else
                                     (FormulaSet.add phi s, phi::ys)
                                 ) (s,[]) (to_conj_list p)
                  in
                    (s', (conj_list (List.rev ys')) :: xs)
                ) (FormulaSet.empty, []) ps
  in
    List.rev xs


let required_sorts (phi:formula) : sort list =
  let empty = SortSet.empty in
  let union = SortSet.union in
  let add = SortSet.add in
  let single = SortSet.singleton in
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

  and req_a (a:addr) : SortSet.t =
    match a with
    | VarAddr _             -> single Addr
    | Null                  -> single Addr
    | Next c                -> append Addr [req_c c]
    | NextAt (c,l)          -> append Addr [req_c c;req_i l]
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
    | VarTh _            -> single Thid
    | NoThid             -> single Thid
    | CellLockId c       -> append Thid [req_c c]
    | CellLockIdAt (c,l) -> append Thid [req_c c;req_i l]
    | ThidArrayRd (a,t)  -> append Thid [req_arr a;req_t t]
    | ThidArrRd (a,l)    -> append Thid [req_tidarr a;req_i l]

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
    | VarT (_,s,_,_,_,_) -> single s
    | SetT s             -> req_s s
    | ElemT e            -> req_e e
    | ThidT t            -> req_t t
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
                   (ignore_xs:pc_t list) : pc_t list =
  let full_xs = LeapLib.rangeList 0 max_pos in
  let base_pos_list = if focus_xs = [] then full_xs else focus_xs in
  let base_pos_set = List.fold_left (fun s p ->
                         PosSet.add p s
                     ) PosSet.empty base_pos_list in
  let focus_set = List.fold_left (fun s p ->
                    PosSet.remove p s
                  ) base_pos_set ignore_xs in
    (PosSet.elements focus_set)

