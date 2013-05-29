open Printf
open LeapLib


module type S =
  sig

    type varId = string

    type var_info_t

    type variable = varId * sort * bool * tid option * string option * var_info_t

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
      | Level
      | Bool
      | Unknown
    and term =
        VarT              of variable
      | SetT              of set
      | ElemT             of elem
      | ThidT             of tid
      | AddrT             of addr
      | CellT             of cell
      | SetThT            of setth
      | SetElemT          of setelem
      | PathT             of path
      | MemT              of mem
      | LevelT            of level
      | VarUpdate         of variable * tid * term
    and eq = term * term
    and diseq = term * term
    and set =
        VarSet            of variable
      | EmptySet
      | Singl             of addr
      | Union             of set * set
      | Intr              of set * set
      | Setdiff           of set * set
      | PathToSet         of path
      | AddrToSet         of mem * addr * level
    and tid =
        VarTh             of variable
      | NoThid
      | CellLockIdAt      of cell * level
    and elem =
        VarElem           of variable
      | CellData          of cell
      | HavocSkiplistElem
      | LowestElem
      | HighestElem
    and addr =
        VarAddr           of variable
      | Null
      | NextAt            of cell * level
      | FirstLockedAt     of mem * path * level
    (*  | Malloc of elem * addr * tid *)
    and cell =
        VarCell           of variable
      | Error
      | MkCell            of elem * addr list * tid list
      | CellLockAt        of cell * level * tid
      | CellUnlockAt      of cell * level
      | CellAt            of mem * addr
    and setth =
        VarSetTh          of variable
      | EmptySetTh
      | SinglTh           of tid
      | UnionTh           of setth * setth
      | IntrTh            of setth * setth
      | SetdiffTh         of setth * setth
    and setelem =
        VarSetElem        of variable
      | EmptySetElem
      | SinglElem         of elem
      | UnionElem         of setelem * setelem
      | IntrElem          of setelem * setelem
      | SetToElems        of set * mem
      | SetdiffElem       of setelem * setelem
    and path =
        VarPath           of variable
      | Epsilon
      | SimplePath        of addr
      | GetPathAt         of mem * addr * addr * level
    and mem =
        VarMem            of variable
      | Emp
      | Update            of mem * addr * cell
    and level =
        LevelVal          of int
      | VarLevel          of variable
      | LevelSucc         of level
      | LevelPred         of level
      | HavocLevel
    and atom =
        Append            of path * path * path
      | Reach             of mem * addr * addr * level * path
      | OrderList         of mem * addr * addr
      | In                of addr * set
      | SubsetEq          of set  * set
      | InTh              of tid * setth
      | SubsetEqTh        of setth * setth
      | InElem            of elem * setelem
      | SubsetEqElem      of setelem * setelem
      | Less              of level * level
      | Greater           of level * level
      | LessEq            of level * level
      | GreaterEq         of level * level
      | LessElem          of elem * elem
      | GreaterElem       of elem * elem
      | Eq                of eq
      | InEq              of diseq
      | BoolVar           of variable
      | PC                of int * tid option * bool
      | PCUpdate          of int * tid
      | PCRange           of int * int * tid option * bool
    and literal =
        Atom              of atom
      | NegAtom           of atom
    and conjunctive_formula =
        FalseConj
      | TrueConj
      | Conj              of literal list
    and disjunctive_formula =
      | FalseDisj
      | TrueDisj
      | Disj              of literal list
    and formula =
        Literal           of literal
      | True
      | False
      | And               of formula * formula
      | Or                of formula * formula
      | Not               of formula
      | Implies           of formula * formula
      | Iff               of formula * formula


    type special_op_t =
      | Reachable
      | Addr2Set
      | Path2Set
      | FstLocked
      | Getp
      | Set2Elem
      | ElemOrder
      | LevelOrder
      | OrderedList


    exception WrongType of term

    (* CALCULATE SET OF VARS *)
    module VarIdSet : Set.S with type elt = varId
    module VarSet : Set.S with type elt = variable
    module TermSet : Set.S with type elt = term
    module AtomSet : Set.S with type elt = atom
    module ThreadSet : Set.S with type elt = tid

    (* Expression height *)
    val k : int

    (* Variable construction *)
    val build_var : varId -> sort -> bool -> tid option -> string option -> variable

    (* variable manipulation *)
    val param_var : variable -> tid -> variable
    val is_global_var : variable -> bool
    val get_sort : variable -> sort

    (* returns all variables form a formula *)
    val get_varlist_from_conj : conjunctive_formula -> variable list
    val get_varlist_of_sort_from_conj : conjunctive_formula -> sort -> varId list
    val varlist_of_sort : variable list -> sort -> varId list

    val get_varset_from_conj         : conjunctive_formula -> VarSet.t
    val get_unparam_varset_from_conj : conjunctive_formula -> VarSet.t
    val get_varset_from_formula      : formula -> VarSet.t
    val get_unparam_varset_from_formula      : formula -> VarSet.t
    val get_varset_of_sort_from_conj : conjunctive_formula -> sort -> VarSet.t
    val varset_of_sort               : VarSet.t -> sort -> VarSet.t
    val get_termset_from_formula     : formula -> TermSet.t
    val get_termset_from_conjformula : conjunctive_formula -> TermSet.t
    val termset_of_sort              : TermSet.t -> sort -> TermSet.t

    
    val remove_nonparam_local_vars : VarSet.t -> VarSet.t
    val add_prevstate_local_vars : VarSet.t -> VarSet.t

    val voc_term : term -> tid list
    val voc : formula -> tid list
    val conjformula_voc : conjunctive_formula -> tid list
    val unprimed_voc : formula -> tid list

    val nnf : formula -> formula
    val dnf : formula -> conjunctive_formula list
    val cnf : formula -> disjunctive_formula list

    val prime_var : variable -> variable
    val unprime_var : variable -> variable
    val is_primed_var : variable -> bool
    val variable_mark_smp_interesting : variable -> bool -> unit
    val variable_mark_fresh : variable -> bool -> unit
    val variable_is_smp_interesting : variable -> bool
    val variable_is_fresh : variable -> bool

    (* SMP MARKING FUNCTIONS *)
    val addr_mark_smp_interesting : addr -> bool -> unit
    val tid_mark_smp_interesting : tid -> bool -> unit


    (* PRETTY_PRINTERS *)
    val variable_to_full_str : variable -> string
    val variable_to_str : variable -> string
    val atom_to_str     : atom    -> string
    val literal_to_str  : literal -> string
    val conjunctive_formula_to_str : conjunctive_formula -> string
    val disjunctive_formula_to_str : disjunctive_formula -> string
    val term_to_str     : term   -> string
    val addr_to_str     : addr   -> string
    val cell_to_str     : cell   -> string
    val elem_to_str     : elem   -> string
    val tid_to_str      : tid   -> string
    val mem_to_str      : mem    -> string
    val path_to_str     : path   -> string
    val set_to_str      : set    -> string
    val setth_to_str    : setth  -> string
    val formula_to_str  : formula -> string

    (* val eq_to_str      : eq     -> string *)
    (* val diseq_to_str   : diseq  -> string *)

    val sort_to_str : sort -> string
    val variable_list_to_str : varId list -> string
    val typed_variable_list_to_str : (varId * sort) list -> string

    val variable_set_to_str : VarIdSet.t -> string
    val typed_variable_set_to_str : VarSet.t -> string


    val print_formula : formula -> unit
    val print_conjunctive_formula: conjunctive_formula -> unit
    val print_atom    : atom    -> unit
    val print_literal : literal -> unit
    val print_addr  : addr  -> unit
    val print_cell  : cell  -> unit
    val print_elem  : elem  -> unit
    val print_tid  : tid  -> unit
    val print_mem   : mem   -> unit
    val print_path  : path  -> unit
    val print_set   : set   -> unit
    val print_setth : setth -> unit
    val print_variable_list : varId list -> unit
    val print_typed_variable_list : (varId * sort) list -> unit
    val print_variable_set : VarIdSet.t -> unit
    val print_typed_variable_set : VarSet.t -> unit
      
    val generic_printer : ('a -> string) -> 'a -> unit

    val split_conj : formula -> formula list

    val required_sorts : formula -> sort list
    val special_ops : formula -> special_op_t list

    val cleanup_dup : conjunctive_formula -> conjunctive_formula

    val get_addrs_eqs_conj : conjunctive_formula -> ((addr*addr) list * (addr*addr) list)
    val get_addrs_eqs : formula -> ((addr*addr) list * (addr*addr) list)

    val conj_list : formula list -> formula
    val disj_list : formula list -> formula
    val to_conj_list : formula -> formula list
    val to_disj_list : formula -> formula list


    (* Equality constructor functions for formulas *)
    val eq_set : set -> set -> formula
    val eq_elem : elem -> elem -> formula
    val eq_tid : tid -> tid -> formula
    val eq_addr : addr -> addr -> formula
    val eq_cell : cell -> cell -> formula
    val eq_setth : setth -> setth -> formula
    val eq_setelem : setelem -> setelem -> formula
    val eq_path : path -> path -> formula
    val eq_mem : mem -> mem -> formula
    val eq_level : level -> level -> formula
    val eq_term : term -> term -> formula
    val ineq_set : set -> set -> formula
    val ineq_elem : elem -> elem -> formula
    val ineq_tid : tid -> tid -> formula
    val ineq_addr : addr -> addr -> formula
    val ineq_cell : cell -> cell -> formula
    val ineq_setth : setth -> setth -> formula
    val ineq_setelem : setelem -> setelem -> formula
    val ineq_path : path -> path -> formula
    val ineq_mem : mem -> mem -> formula
    val ineq_level : level -> level -> formula
    val ineq_term : term -> term -> formula
    val less_level : level -> level -> formula
    val lesseq_level : level -> level -> formula
    val greater_level : level -> level -> formula
    val greatereq_level : level -> level -> formula
    val subseteq : set -> set -> formula
    val atomlit : atom -> formula
  end


module Make (K : Level.S) : S =
  struct

    type varId = string

    type var_info_t =
      {
        mutable smp_interesting : bool;
        mutable fresh : bool;
      }

    type variable = varId * sort * bool * tid option * string option * var_info_t

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
      | Level
      | Bool
      | Unknown
    and term =
        VarT              of variable
      | SetT              of set
      | ElemT             of elem
      | ThidT             of tid
      | AddrT             of addr
      | CellT             of cell
      | SetThT            of setth
      | SetElemT          of setelem
      | PathT             of path
      | MemT              of mem
      | LevelT            of level
      | VarUpdate         of variable * tid * term
    and eq = term * term
    and diseq = term * term
    and set =
        VarSet            of variable
      | EmptySet
      | Singl             of addr
      | Union             of set * set
      | Intr              of set * set
      | Setdiff           of set * set
      | PathToSet         of path
      | AddrToSet         of mem * addr * level
    and tid =
        VarTh             of variable
      | NoThid
      | CellLockIdAt      of cell * level
    and elem =
        VarElem           of variable
      | CellData          of cell
      | HavocSkiplistElem
      | LowestElem
      | HighestElem
    and addr =
        VarAddr           of variable
      | Null
      | NextAt            of cell * level
      | FirstLockedAt     of mem * path * level
    (*  | Malloc of elem * addr * tid *)
    and cell =
        VarCell           of variable
      | Error
      | MkCell            of elem * addr list * tid list
      | CellLockAt        of cell * level * tid
      | CellUnlockAt      of cell * level
      | CellAt            of mem * addr
    and setth =
        VarSetTh          of variable
      | EmptySetTh
      | SinglTh           of tid
      | UnionTh           of setth * setth
      | IntrTh            of setth * setth
      | SetdiffTh         of setth * setth
    and setelem =
        VarSetElem        of variable
      | EmptySetElem
      | SinglElem         of elem
      | UnionElem         of setelem * setelem
      | IntrElem          of setelem * setelem
      | SetToElems        of set * mem
      | SetdiffElem       of setelem * setelem
    and path =
        VarPath           of variable
      | Epsilon
      | SimplePath        of addr
      | GetPathAt         of mem * addr * addr * level
    and mem =
        VarMem            of variable
      | Emp
      | Update            of mem * addr * cell
    and level =
        LevelVal          of int
      | VarLevel          of variable
      | LevelSucc         of level
      | LevelPred         of level
      | HavocLevel
    and atom =
        Append            of path * path * path
      | Reach             of mem * addr * addr * level * path
      | OrderList         of mem * addr * addr
      | In                of addr * set
      | SubsetEq          of set  * set
      | InTh              of tid * setth
      | SubsetEqTh        of setth * setth
      | InElem            of elem * setelem
      | SubsetEqElem      of setelem * setelem
      | Less              of level * level
      | Greater           of level * level
      | LessEq            of level * level
      | GreaterEq         of level * level
      | LessElem          of elem * elem
      | GreaterElem       of elem * elem
      | Eq                of eq
      | InEq              of diseq
      | BoolVar           of variable
      | PC                of int * tid option * bool
      | PCUpdate          of int * tid
      | PCRange           of int * int * tid option * bool
    and literal =
        Atom              of atom
      | NegAtom           of atom
    and conjunctive_formula =
        FalseConj
      | TrueConj
      | Conj              of literal list
    and disjunctive_formula =
      | FalseDisj
      | TrueDisj
      | Disj              of literal list
    and formula =
        Literal           of literal
      | True
      | False
      | And               of formula * formula
      | Or                of formula * formula
      | Not               of formula
      | Implies           of formula * formula
      | Iff               of formula * formula

    type special_op_t =
      | Reachable
      | Addr2Set
      | Path2Set
      | FstLocked
      | Getp
      | Set2Elem
      | ElemOrder
      | LevelOrder
      | OrderedList

    exception WrongType of term


    let k = K.level

    (*************************)
    (* VARIABLE MANIPULATION *)
    (*************************)

    let build_var (id:varId)
                  (s:sort)
                  (pr:bool)
                  (th:tid option)
                  (p:string option) : variable =
      (id,s,pr,th,p,{smp_interesting=false;fresh=false;})


    let param_var (v:variable) (th:tid) : variable =
      let (id,s,pr,_,p,info) = v
      in
        (id,s,pr,Some th,p,info)


    let unparam_var (v:variable) : variable =
      let (id,s,pr,_,p,info) = v
      in
        (id,s,pr,None,p,info)


    let is_global_var (v:variable) : bool =
      let (_,_,_,_,p,_) = v in p = None


    let get_sort (v:variable) : sort =
      let (_,s,_,_,_,_) = v in s


    let prime_var (v:variable) : variable =
      let (id,s,_,th,p,info) = v in (id,s,true,th,p,info)


    let unprime_var (v:variable) : variable =
      let (id,s,_,th,p,info) = v in (id,s,false,th,p,info)


    let is_primed_var (v:variable) : bool =
      let (_,_,pr,_,_,_) = v in
        pr

    let variable_mark_smp_interesting (v:variable) (b:bool) : unit =
      let (_,_,_,_,_,info) = v in
        info.smp_interesting <- b

    let variable_mark_fresh (v:variable) (b:bool) : unit =
      let (_,_,_,_,_,info) = v in
        info.fresh <- b

    let variable_is_smp_interesting (v:variable) : bool =
      let (_,_,_,_,_,info) = v in info.smp_interesting

    let variable_is_fresh (v:variable) : bool =
(*    Correct way *)
(*    let (_,_,_,_,_,info) = v in info.fresh *)
      let (id,_,_,_,_,info) = v in (id.[0] = '$' || info.fresh)


    let is_primed_tid (th:tid) : bool =
      match th with
      | VarTh v           -> is_primed_var v
      | NoThid            -> false
      | CellLockIdAt _    -> false
      (* FIX: Propagate the query inside cell??? *)


    let var_th (v:variable) : tid option =
      let (_,_,_,th,_,_) = v in th


    let variable_clean_info (v:variable) : unit =
      let (_,_,_,_,_,info) = v in
        info.fresh <- false;
        info.smp_interesting <- false


    let unify_var_info (info1:var_info_t) (info2:var_info_t) : var_info_t =
      {
        fresh = (info1.fresh || info2.fresh);
        smp_interesting = (info1.smp_interesting || info2.smp_interesting);
      }


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


    let unify_varset (s:S.t) : S.t =
      let tbl = Hashtbl.create (S.cardinal s) in
      S.iter (fun (id,s,pr,th,p,info) ->
        let base = (id,s,pr,th,p) in
        if Hashtbl.mem tbl base then
          let prev_info = Hashtbl.find tbl base in
          Hashtbl.replace tbl base (unify_var_info info prev_info)
        else
          Hashtbl.add tbl base info
      ) s;
      Hashtbl.fold (fun (id,s,pr,th,p) info set -> S.add (id,s,pr,th,p,info) set) tbl S.empty


    let remove_nonparam_local_vars (s:S.t) : S.t =
      S.fold (fun v tmpset ->
        if not (is_global_var v) && var_th v = None then
          tmpset
        else
          S.add v tmpset
      ) s S.empty


    let unparam_varset (s:S.t) : S.t =
      S.fold (fun v tmpset ->
        S.add (unparam_var v) tmpset
      ) s S.empty


    let add_prevstate_local_vars (s:S.t) : S.t =
      S.fold (fun v tmpset ->
        let unprime_v = unprime_var v in
        if is_primed_var v && not (S.mem unprime_v s) then
          S.add v (S.add unprime_v tmpset)
        else
          S.add v tmpset
      ) s S.empty


    let (@@) s1 s2 =
      S.union s1 s2

    let get_varset_from_param (v:variable) : S.t =
      let (_,_,_,th,_,_) = v
      in
        match th with
          Some (VarTh t) -> S.singleton t
        | _              -> S.empty


    let rec get_varset_set s =
      match s with
          VarSet v         -> S.singleton v @@ get_varset_from_param v
        | EmptySet         -> S.empty
        | Singl(a)         -> get_varset_addr a
        | Union(s1,s2)     -> (get_varset_set s1) @@ (get_varset_set s2)
        | Intr(s1,s2)      -> (get_varset_set s1) @@ (get_varset_set s2)
        | Setdiff(s1,s2)   -> (get_varset_set s1) @@ (get_varset_set s2)
        | PathToSet(p)     -> get_varset_path p
        | AddrToSet(m,a,l) -> (get_varset_mem m)  @@
                              (get_varset_addr a) @@
                              (get_varset_level l)
    and get_varset_tid th =
      match th with
          VarTh v            -> S.singleton v @@ get_varset_from_param v
        | NoThid             -> S.empty
        | CellLockIdAt (c,l) -> (get_varset_cell c) @@ (get_varset_level l)
    and get_varset_elem e =
      match e with
          VarElem v         -> S.singleton v @@ get_varset_from_param v
        | CellData c        -> get_varset_cell c
        | HavocSkiplistElem -> S.empty
        | LowestElem        -> S.empty
        | HighestElem       -> S.empty
    and get_varset_addr a =
      match a with
          VarAddr v            -> S.singleton v @@ get_varset_from_param v
        | Null                 -> S.empty
        | NextAt (c,l)         -> (get_varset_cell c) @@ (get_varset_level l)
        | FirstLockedAt(m,p,l) -> (get_varset_mem m) @@ (get_varset_path p) @@
                                  (get_varset_level l)
    (*    | Malloc(e,a,th)   -> (get_varset_elem e) @@ (get_varset_addr a) @@  (get_varset_tid th) *)
    and get_varset_cell c =
      let fold f xs = List.fold_left (fun set x -> (f x) @@ set) S.empty xs in
      match c with
          VarCell v           -> S.singleton v @@ get_varset_from_param v
        | Error               -> S.empty
        | MkCell(e,aa,tt)     -> (get_varset_elem e) @@
                                 (fold get_varset_addr aa) @@
                                 (fold get_varset_tid tt)
        | CellLockAt (c,l,th) -> (get_varset_cell c) @@ (get_varset_level l) @@
                                 (get_varset_tid th)
        | CellUnlockAt (c,l)  -> (get_varset_cell c) @@ (get_varset_level l)
        | CellAt(m,a)         -> (get_varset_mem  m) @@ (get_varset_addr a)
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
          VarPath v            -> S.singleton v @@ get_varset_from_param v
        | Epsilon              -> S.empty
        | SimplePath(a)        -> (get_varset_addr a)
        | GetPathAt(m,a1,a2,l) -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                  (get_varset_addr a2) @@ (get_varset_level l)
    and get_varset_mem m =
      match m with
          VarMem v           -> S.singleton v @@ get_varset_from_param v
        | Emp                -> S.empty
        | Update(m,a,c)      -> (get_varset_mem m) @@ (get_varset_addr a) @@ (get_varset_cell c)
    and get_varset_level i =
      match i with
          LevelVal _  -> S.empty
        | VarLevel v  -> S.singleton v
        | LevelSucc l -> (get_varset_level l)
        | LevelPred l -> (get_varset_level l)
        | HavocLevel  -> S.empty
    and get_varset_atom a =
      match a with
          Append(p1,p2,p3)       -> (get_varset_path p1) @@ (get_varset_path p2) @@
                                    (get_varset_path p3)
        | Reach(m,a1,a2,l,p)     -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                    (get_varset_addr a2) @@ (get_varset_level l) @@
                                    (get_varset_path p)
        | OrderList(m,a1,a2)     -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                    (get_varset_addr a2)
        | In(a,s)                -> (get_varset_addr a) @@ (get_varset_set s)
        | SubsetEq(s1,s2)        -> (get_varset_set s1) @@ (get_varset_set s2)
        | InTh(th,st)            -> (get_varset_tid th) @@ (get_varset_setth st)
        | SubsetEqTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
        | InElem(e,se)           -> (get_varset_elem e) @@ (get_varset_setelem se)
        | SubsetEqElem(se1,se2)  -> (get_varset_setelem se1) @@
                                    (get_varset_setelem se2)
        | Less (i,j)             -> (get_varset_level i) @@ (get_varset_level j)
        | Greater (i,j)          -> (get_varset_level i) @@ (get_varset_level j)
        | LessEq (i,j)           -> (get_varset_level i) @@ (get_varset_level j)
        | GreaterEq (i,j)        -> (get_varset_level i) @@ (get_varset_level j)
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
        | LevelT l            -> get_varset_level l
        | VarUpdate(v,pc,t)   -> (S.singleton v) @@ (get_varset_term t) @@
                                 (get_varset_from_param v)
    and get_varset_literal l =
      match l with
          Atom a    -> get_varset_atom a
        | NegAtom a -> get_varset_atom a

    and get_varset_from_conj_aux phi =
      let another_lit vars alit = vars @@ (get_varset_literal alit) in
      match phi with
          TrueConj   -> S.empty
        | FalseConj  -> S.empty
        | Conj l     -> List.fold_left (another_lit) S.empty l

    and get_varset_from_conj phi =
      unify_varset (get_varset_from_conj_aux phi)

    and get_unparam_varset_from_conj phi =
      unify_varset (unparam_varset (get_varset_from_conj_aux phi))

    and get_varset_from_formula_aux phi =
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

    and get_varset_from_formula phi =
      unify_varset (get_varset_from_formula_aux phi)

    and get_unparam_varset_from_formula phi =
      unify_varset (unparam_varset (get_varset_from_formula_aux phi))


    let localize_with_underscore (v:varId) (p_name:string option) : string =
      let p_str = Option.map_default (fun p -> p^"_") "" p_name
      in
        sprintf "%s%s" p_str v


    let varset_of_sort all s =
      let filt (v,asort,pr,th,p,info) res =
        if asort=s then
          VarSet.add (v,asort,pr,None,p,info) res
    (*      VarSet.add ((localize_with_underscore v p) res *)
        else
          res in
        S.fold filt all VarSet.empty

    let get_varset_of_sort_from_conj phi s =
      varset_of_sort (get_varset_from_conj phi) s


    let get_varlist_from_conj phi =
      S.elements (get_varset_from_conj phi)

    let varlist_of_sort varlist s =
      let is_s (_,asort,_,_,_,_) = (asort=s) in
      List.map (fun (v,_,_,_,p,_) -> (localize_with_underscore v p))
               (List.filter is_s varlist)

    let get_varlist_of_sort_from_conj phi s =
      varlist_of_sort (get_varlist_from_conj phi) s


    (* TOFIX: terms may be considered different if they differ just in the
              variable information stored in the var_info_t *)
    let rec get_termset_atom (a:atom) : TermSet.t =
      let add_list = List.fold_left (fun s e -> TermSet.add e s) TermSet.empty in
      match a with
      | Append(p1,p2,p3)       -> add_list [PathT p1; PathT p2; PathT p3]
      | Reach(m,a1,a2,l,p)     -> add_list [MemT m; AddrT a1; AddrT a2; LevelT l; PathT p]
      | OrderList(m,a1,a2)     -> add_list [MemT m; AddrT a1; AddrT a2]
      | In(a,s)                -> add_list [AddrT a; SetT s]
      | SubsetEq(s1,s2)        -> add_list [SetT s1; SetT s2]
      | InTh(th,st)            -> add_list [ThidT th; SetThT st]
      | SubsetEqTh(st1,st2)    -> add_list [SetThT st1; SetThT st2]
      | InElem(e,se)           -> add_list [ElemT e; SetElemT se]
      | SubsetEqElem(se1,se2)  -> add_list [SetElemT se1; SetElemT se2]
      | Less (l1,l2)           -> add_list [LevelT l1; LevelT l2]
      | Greater (l1,l2)        -> add_list [LevelT l1; LevelT l2]
      | LessEq (l1,l2)         -> add_list [LevelT l1; LevelT l2]
      | GreaterEq (l1,l2)      -> add_list [LevelT l1; LevelT l2]
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
        | Set       -> (match t with | SetT _       -> true | _ -> false)
        | Elem      -> (match t with | ElemT _      -> true | _ -> false)
        | Thid      -> (match t with | ThidT _      -> true | _ -> false)
        | Addr      -> (match t with | AddrT _      -> true | _ -> false)
        | Cell      -> (match t with | CellT _      -> true | _ -> false)
        | SetTh     -> (match t with | SetThT _     -> true | _ -> false)
        | SetElem   -> (match t with | SetElemT _   -> true | _ -> false)
        | Path      -> (match t with | PathT _      -> true | _ -> false)
        | Mem       -> (match t with | MemT _       -> true | _ -> false)
        | Level     -> (match t with | LevelT _     -> true | _ -> false)
        | Bool      -> (match t with | VarT v -> get_sort v = Bool
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
    and is_int_var s =
      match s with
          VarLevel _ -> true | _ -> false

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
        | LevelT _         -> Level
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
          VarT(_)        -> true
        | SetT s         -> is_set_flat s
        | ElemT e        -> is_elem_flat   e
        | ThidT k        -> is_tid_flat k
        | AddrT a        -> is_addr_flat a
        | CellT c        -> is_cell_flat c
        | SetThT st      -> is_setth_flat st
        | SetElemT se    -> is_setelem_flat se
        | PathT p        -> is_path_flat p
        | MemT  m        -> is_mem_flat m
        | LevelT  i      -> is_level_flat i
        | VarUpdate _    -> true
    and is_set_flat t =
      match t with
          VarSet _         -> true
        | EmptySet         -> true
        | Singl(a)         -> is_addr_var  a
        | Union(s1,s2)     -> (is_set_var s1) && (is_set_var s2)
        | Intr(s1,s2)      -> (is_set_var s1) && (is_set_var s2)
        | Setdiff(s1,s2)   -> (is_set_var s1) && (is_set_var s2)
        | PathToSet(p)     -> (is_path_var p)
        | AddrToSet(m,a,l) -> (is_mem_var m)  &&
                              (is_addr_var a) &&
                              (is_int_var l)
    and is_tid_flat t =
      match t with
          VarTh _            -> true
        | NoThid             -> true
        | CellLockIdAt (c,l) -> (is_cell_var c) && (is_int_var l)
    and is_elem_flat t =
      match t with
          VarElem _         -> true
        | CellData(c)       -> is_cell_var c
        | HavocSkiplistElem -> true
        | LowestElem        -> true
        | HighestElem       -> true
    and is_addr_flat t =
      match t with
          VarAddr _            -> true
        | Null                 -> true
        | NextAt(c,l)          -> (is_cell_var c) && (is_int_var l)
        | FirstLockedAt(m,p,l) -> (is_mem_var m) && (is_path_var p) && (is_int_var l)
    (*    | Malloc(m,a,k)    -> (is_mem_var m) && (is_addr_var a) && (is_thread_var k) *)
    and is_cell_flat t =
      match t with
          VarCell _           -> true
        | Error               -> true
        | MkCell (e,aa,tt)    -> (is_elem_var e) &&
                                 (List.for_all is_addr_var aa) &&
                                 (List.for_all is_tid_var tt)
        | CellLockAt (c,l,th) -> (is_cell_var c) && (is_int_var l) && (is_tid_var th)
        | CellUnlockAt (c,l)  -> (is_cell_var c) && (is_int_var l)
        | CellAt(m,a)         -> (is_mem_var m) && (is_addr_var a)
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
          VarPath _            -> true
        | Epsilon              -> true
        | SimplePath(a)        -> is_addr_var a
        | GetPathAt(m,a1,a2,l) -> (is_mem_var m) && (is_addr_var a1) &&
                                  (is_addr_var a2) && (is_int_var l)
    and is_mem_flat t =
      match t with
          VarMem _ -> true
        | Emp      -> true
        | Update(m,a,c) -> (is_mem_var m) && (is_addr_var a) && (is_cell_var c)
    and is_level_flat t =
      match t with
          LevelVal _  -> true
        | VarLevel _  -> true
        | LevelSucc l -> is_level_flat l
        | LevelPred l -> is_level_flat l
        | HavocLevel   -> true

    let is_literal_flat lit =
      match lit with
          Atom a ->
      begin match a with
        | Append(p1,p2,p3)       -> (is_path_var p1) && (is_path_var p2) &&
                                    (is_path_var p3)
        | Reach(m,a1,a2,l,p)     -> (is_mem_var m) && (is_addr_var a1) &&
                                    (is_addr_var a2) && (is_int_var l) &&
                                    (is_path_var p)
        | OrderList(m,a1,a2)     -> (is_mem_var m) && (is_addr_var a1) &&
                                    (is_addr_var a2)
        | In(a,s)                -> (is_addr_var a) && (is_set_var s)
        | SubsetEq(s1,s2)        -> (is_set_var s1) && (is_set_var s2)
        | InTh(k,st)             -> (is_tid_var k) && (is_setth_var st)
        | SubsetEqTh(st1,st2)    -> (is_setth_var st1) && (is_setth_var st2)
        | InElem(e,se)           -> (is_elem_var e) && (is_setelem_var se)
        | SubsetEqElem(se1,se2)  -> (is_setelem_var se1) && (is_setelem_var se2)
        | Less (i1,i2)           -> (is_int_var i1) && (is_int_var i2)
        | Greater (i1,i2)        -> (is_int_var i1) && (is_int_var i2)
        | LessEq (i1,i2)         -> (is_int_var i1) && (is_int_var i2)
        | GreaterEq (i1,i2)      -> (is_int_var i1) && (is_int_var i2)
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
        | Reach(m,a1,a2,l,p)    -> (is_mem_var m) && (is_addr_var a1) &&
                                   (is_addr_var a2) && (is_int_var l) &&
                                   (is_path_var p)
        | OrderList(m,a1,a2)    -> (is_mem_var m) && (is_addr_var a1) &&
                                   (is_addr_var a2)
        | In(a,s)               -> (is_addr_var a) && (is_set_var s)
        | SubsetEq(s1,s2)       -> (is_set_var s1) && (is_set_var s2)
        | InTh(k,st)            -> (is_tid_var k) && (is_setth_var st)
        | SubsetEqTh(st1,st2)   -> (is_setth_var st1) && (is_setth_var st2)
        | InElem(e,se)          -> (is_elem_var e) && (is_setelem_var se)
        | SubsetEqElem(se1,se2) -> (is_setelem_var se1) && (is_setelem_var se2)
        | Less (i1,i2)          -> (is_int_var i1) && (is_int_var i2)
        | Greater (i1,i2)       -> (is_int_var i1) && (is_int_var i2)
        | LessEq (i1,i2)        -> (is_int_var i1) && (is_int_var i2)
        | GreaterEq (i1,i2)     -> (is_int_var i1) && (is_int_var i2)
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


    let sort_to_str s =
      match s with
          Set       -> "Set"
        | Elem      -> "Elem"
        | Thid      -> "Thid"
        | Addr      -> "Addr"
        | Cell      -> "Cell"
        | SetTh     -> "SetTh"
        | SetElem   -> "SetElem"
        | Path      -> "Path"
        | Mem       -> "Mem"
        | Level     -> "Level"
        | Bool      -> "Bool"
        | Unknown   -> "Unknown"


    let rec variable_to_full_str (v:variable) : string =
      let (id,s,pr,th,p,info) = v in
      "Variable " ^variable_to_str v^ " information\n" ^
      "Id:              " ^id^ "\n" ^
      "Sort:            " ^sort_to_str s^ "\n" ^
      "Primed:          " ^if pr then "true" else "false"^ "\n" ^
      "Thread:          " ^Option.map_default tid_to_str "None" th^ "\n" ^
      "Parent:          " ^Option.default "None" p^ "\n" ^
      "SMP Interesting: " ^if info.smp_interesting then "true" else "false"^ "\n" ^
      "Fresh:           " ^if info.fresh then "true" else "false"^ "\n"
(*
        (variable_to_str v) (id) (sort_to_str s) (pr) (Option.map tid_to_str "None" th)
        (Option.default "None" p) (info.smp_interesting) (info.fresh)
*)


    and variable_to_str (v:variable) : string =
      let (id,_,pr,th,p,_) = v in
      let v_str = sprintf "%s%s" (Option.map_default (localize_var_id id) id p)
                                 (Option.map_default (fun t -> "(" ^ tid_to_str t ^ ")" ) "" th)
      in
        if pr then v_str ^ "'" else v_str

    and atom_to_str a =
      match a with
      | Append(p1,p2,pres)         -> Printf.sprintf "append(%s,%s,%s)"
                                        (path_to_str p1) (path_to_str p2)
                                        (path_to_str pres)
      | Reach(h,a_from,a_to,l,p)   -> Printf.sprintf "reach(%s,%s,%s,%s,%s)"
                                        (mem_to_str h) (addr_to_str a_from)
                                        (addr_to_str a_to) (level_to_str l)
                                        (path_to_str p)
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
                                        (level_to_str i1) (level_to_str i2)
      | Greater (i1,i2)            -> Printf.sprintf "%s > %s"
                                        (level_to_str i1) (level_to_str i2)
      | LessEq (i1,i2)             -> Printf.sprintf "%s <= %s"
                                        (level_to_str i1) (level_to_str i2)
      | GreaterEq (i1,i2)          -> Printf.sprintf "%s >= %s"
                                        (level_to_str i1) (level_to_str i2)
      | LessElem(e1,e2)            -> Printf.sprintf "%s < %s"
                                        (elem_to_str e1) (elem_to_str e2)
      | GreaterElem(e1,e2)         -> Printf.sprintf "%s > %s"
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
    and level_to_str expr =
      match expr with
          LevelVal n       -> string_of_int n
        | VarLevel v       -> variable_to_str v
        | LevelSucc l -> Printf.sprintf "succ (%s)" (level_to_str l)
        | LevelPred l -> Printf.sprintf "pred (%s)" (level_to_str l)
        | HavocLevel     -> Printf.sprintf "havocLevel()"
    and path_to_str expr =
      match expr with
          VarPath(v)                       -> variable_to_str v
        | Epsilon                          -> Printf.sprintf "epsilon"
        | SimplePath(addr)                 -> Printf.sprintf "[ %s ]" (addr_to_str addr)
        | GetPathAt(mem,add_from,add_to,l) -> Printf.sprintf "getp(%s,%s,%s,%s)"
                                                (mem_to_str mem)
                                                (addr_to_str add_from)
                                                (addr_to_str add_to)
                                                (level_to_str l)
    and set_to_str e =
      match e with
          VarSet(v)             -> variable_to_str v
        | EmptySet              -> "EmptySet"
        | Singl(addr)           -> Printf.sprintf "{ %s }" (addr_to_str addr)
        | Union(s1,s2)          -> Printf.sprintf "%s Union %s"
                                      (set_to_str s1) (set_to_str s2)
        | Intr(s1,s2)           -> Printf.sprintf "%s Intr %s"
                                      (set_to_str s1) (set_to_str s2)
        | Setdiff(s1,s2)        -> Printf.sprintf "%s SetDiff %s"
                                      (set_to_str s1) (set_to_str s2)
        | PathToSet(path)       -> Printf.sprintf "path2set(%s)"
                                      (path_to_str path)
        | AddrToSet(mem,addr,l) -> Printf.sprintf "addr2set(%s,%s,%s)"
                                      (mem_to_str mem) (addr_to_str addr)
                                      (level_to_str l)
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
      let concat f xs = String.concat "," (List.map f xs) in
      match e with
          VarCell(v)            -> variable_to_str v
        | Error                 -> "Error"
        | MkCell(data,aa,tt)    -> Printf.sprintf "mkcell(%s,[%s],[%s])"
                                     (elem_to_str data) (concat addr_to_str aa)
                                     (concat tid_to_str tt)
        | CellLockAt(cell,l,th) -> Printf.sprintf "%s.lock(%s,%s)"
                                     (cell_to_str cell) (level_to_str l) (tid_to_str th)
        | CellUnlockAt(cell,l)  -> Printf.sprintf "%s.unlock(%s)"
                                     (cell_to_str cell) (level_to_str l)
        | CellAt(mem,addr)      -> Printf.sprintf "%s [ %s ]"
                                     (mem_to_str mem) (addr_to_str addr)
    and addr_to_str expr =
      match expr with
          VarAddr(v)                -> variable_to_str v
        | Null                      -> "null"
        | NextAt(cell,l)            -> Printf.sprintf "%s.next(%s)"
                                         (cell_to_str cell) (level_to_str l)
        | FirstLockedAt(mem,path,l) -> Printf.sprintf "firstlocked(%s,%s,%s)"
                                         (mem_to_str mem)
                                         (path_to_str path)
                                         (level_to_str l)
    (*    | Malloc(e,a,t)     -> Printf.sprintf "malloc(%s,%s,%s)" (elem_to_str e) (addr_to_str a) (tid_to_str t) *)
    and tid_to_str th =
      match th with
          VarTh(v)             -> variable_to_str v
        | NoThid               -> Printf.sprintf "NoThid"
        | CellLockIdAt(cell,l) -> Printf.sprintf "%s.lockid(%s)"
                                    (cell_to_str cell) (level_to_str l)
    and eq_to_str expr =
      let (e1,e2) = expr in
        Printf.sprintf "%s = %s" (term_to_str e1) (term_to_str e2)
    and diseq_to_str expr =
      let (e1,e2) = expr in
        Printf.sprintf "%s != %s" (term_to_str e1) (term_to_str e2)
    and elem_to_str elem =
      match elem with
          VarElem(v)         -> variable_to_str v
        | CellData(cell)     -> Printf.sprintf "%s.data" (cell_to_str cell)
        | HavocSkiplistElem  -> "havocSkiplistElem()"
        | LowestElem         -> "lowestElem"
        | HighestElem        -> "highestElem"
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
        | LevelT(i)          -> (level_to_str i)
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
    and disjunctive_formula_to_str form =
      let rec c_to_str f str =
        match f with
          | [] -> str
          | lit::sub ->
              c_to_str sub (Printf.sprintf "%s \\/ %s" str (literal_to_str lit))
      in
        match form with
          | TrueDisj  -> Printf.sprintf "true"
          | FalseDisj -> Printf.sprintf "false"
          | Disj([]) -> ""
          | Disj(lit :: subform) -> c_to_str subform (literal_to_str lit)
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
      let pr (v,s,_,_,_,_) str = (str ^ v ^ ": " ^ (sort_to_str s) ^ "\n") in
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
        | LevelT(i)          -> voc_level i
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
      | AddrToSet(mem,a,l)  -> (voc_mem mem) @ (voc_addr a) @ (voc_level l)


    and voc_addr (a:addr) : tid list =
      match a with
        VarAddr v                 -> Option.map_default (fun x->[x]) [] (var_th v)
      | Null                      -> []
      | NextAt(cell,l)            -> (voc_cell cell) @ (voc_level l)
      | FirstLockedAt(mem,path,l) -> (voc_mem mem) @ (voc_path path) @ (voc_level l)


    and voc_elem (e:elem) : tid list =
      match e with
        VarElem v          -> Option.map_default (fun x->[x]) [] (var_th v)
      | CellData(cell)     -> (voc_cell cell)
      | HavocSkiplistElem  -> []
      | LowestElem         -> []
      | HighestElem        -> []


    and voc_tid (th:tid) : tid list =
      match th with
        VarTh v              -> th :: (Option.map_default (fun x->[x]) [] (var_th v))
      | NoThid               -> []
      | CellLockIdAt(cell,l) -> (voc_cell cell) @ (voc_level l)


    and voc_cell (c:cell) : tid list =
      let fold f xs = List.fold_left (fun ys x -> (f x) @ ys) [] xs in
      match c with
        VarCell v            -> Option.map_default (fun x->[x]) [] (var_th v)
      | Error                -> []
      | MkCell(data,aa,tt)   -> (voc_elem data)    @
                                (fold voc_addr aa) @
                                (fold voc_tid tt)
      | CellLockAt(cell,l,th)-> (voc_cell cell) @ (voc_level l) @ (voc_tid th)
      | CellUnlockAt(cell,l) -> (voc_cell cell) @ (voc_level l)
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
        VarPath v                    -> Option.map_default (fun x->[x]) [] (var_th v)
      | Epsilon                      -> []
      | SimplePath(addr)             -> (voc_addr addr)
      | GetPathAt(mem,a_from,a_to,l) -> (voc_mem mem) @
                                        (voc_addr a_from) @
                                        (voc_addr a_to) @
                                        (voc_level l)


    and voc_mem (m:mem) : tid list =
      match m with
        VarMem v             -> Option.map_default (fun x->[x]) [] (var_th v)
      | Emp                  -> []
      | Update(mem,add,cell) -> (voc_mem mem) @ (voc_addr add) @ (voc_cell cell)


    and voc_level (i:level) : tid list =
      match i with
        LevelVal _  -> []
      | VarLevel v  -> Option.map_default (fun x->[x]) [] (var_th v)
      | LevelSucc l -> voc_level l
      | LevelPred l -> voc_level l
      | HavocLevel  -> []


    and voc_atom (a:atom) : tid list =
      match a with
        Append(p1,p2,pres)         -> (voc_path p1) @
                                      (voc_path p2) @
                                      (voc_path pres)
      | Reach(h,a_from,a_to,l,p)   -> (voc_mem h) @
                                      (voc_addr a_from) @
                                      (voc_addr a_to) @
                                      (voc_level l) @
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
      | Less (i1,i2)               -> (voc_level i1) @ (voc_level i2)
      | Greater (i1,i2)            -> (voc_level i1) @ (voc_level i2)
      | LessEq (i1,i2)             -> (voc_level i1) @ (voc_level i2)
      | GreaterEq (i1,i2)          -> (voc_level i1) @ (voc_level i2)
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


    let rec cnf (expr:formula) : disjunctive_formula list =
      let rec cnf_nnf nnfexpr =
        match nnfexpr with
          Or(e1,e2)  ->
            begin
              match (cnf_nnf e1, cnf_nnf e2) with
                ([TrueDisj],_)  -> [TrueDisj]
              | (_,[TrueDisj])  -> [TrueDisj]
              | ([FalseDisj],x) -> x
              | (x,[FalseDisj]) -> x
              | (e1_cnf, e2_cnf) ->
                    let get_disjuncts d =
                      match d with
                        Disj l -> l
                      | _ -> let msg = "Formula "^(formula_to_str nnfexpr)^" is not in NNF.\n" in
                               raise(ErrorInNNF(msg))
                    in
                    (* here lx and ly  are lists of Disj none of which is 
                     * True or False *)
                    let add_to_all_in_e2 final_list x1 =
                      let lx1 = get_disjuncts x1 in
                      let add_x1 l2 x2 = Disj(lx1 @ (get_disjuncts x2))::l2 in
                      let lst = List.fold_left add_x1 [] e2_cnf in
                        lst @ final_list
                    in
                      List.fold_left add_to_all_in_e2 [] e1_cnf
            end
        | And(e1,e2) ->
            begin
              match (cnf_nnf e1, cnf_nnf e2) with
                ([FalseDisj],_) -> [FalseDisj]
              | (_,[FalseDisj]) -> [FalseDisj]
              | ([TrueDisj],x)  -> x
              | (x,[TrueDisj])  -> x
              | (lx,ly) -> lx @ ly
            end
        | Literal(l) -> [ Disj [ l ]]
        | True       -> [TrueDisj]
        | False      -> [FalseDisj]
        | _          -> let msg = "Formula " ^(formula_to_str nnfexpr)^ " is not in NNF.\n" in
                          raise(ErrorInNNF(msg))
      in
        cnf_nnf (nnf expr)


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
        | Reach (m,a1,a2,l,p) -> list_union [req_m m;req_a a1;req_a a2;req_lv l;req_p p]
        | OrderList (m,a1,a2) -> list_union [req_m m;req_a a1;req_a a2]
        | In (a,s)            -> list_union [req_a a;req_s s]
        | SubsetEq (s1,s2)    -> list_union [req_s s1;req_s s2]
        | InTh (t,s)          -> list_union [req_t t;req_st s]
        | SubsetEqTh (s1,s2)  -> list_union [req_st s1;req_st s2]
        | InElem (e,s)        -> list_union [req_e e;req_se s]
        | SubsetEqElem (s1,s2)-> list_union [req_se s1;req_se s2]
        | Less (i1,i2)        -> list_union [req_lv i1;req_lv i2]
        | Greater (i1,i2)     -> list_union [req_lv i1;req_lv i2]
        | LessEq (i1,i2)      -> list_union [req_lv i1;req_lv i2]
        | GreaterEq (i1,i2)   -> list_union [req_lv i1;req_lv i2]
        | LessElem  (e1,e2)   -> list_union [req_e e1; req_e e2]
        | GreaterElem (e1,e2) -> list_union [req_e e1; req_e e2]
        | Eq (t1,t2)          -> union (req_term t1) (req_term t2)
        | InEq (t1,t2)        -> union (req_term t1) (req_term t2)
        | BoolVar v           -> single Bool
        | PC _                -> single Thid
        | PCUpdate _          -> single Thid
        | PCRange _           -> empty

      and req_m (m:mem) : SortSet.t =
        match m with
        | VarMem _         -> single Mem
        | Emp              -> single Mem
        | Update (m,a,c)   -> append Mem [req_m m;req_a a;req_c c]

      and req_lv (l:level) : SortSet.t =
        match l with
        | LevelVal _  -> single Level
        | VarLevel _  -> single Level
        | LevelSucc l -> append Level [req_lv l]
        | LevelPred l -> append Level [req_lv l]
        | HavocLevel  -> empty

      and req_p (p:path) : SortSet.t =
        match p with
        | VarPath _             -> single Path
        | Epsilon               -> single Path
        | SimplePath a          -> append Path [req_a a]
        | GetPathAt (m,a1,a2,l) -> append Path [req_m m;req_a a1;req_a a2;req_lv l]

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
        | MkCell (e,aa,tt)   -> append Cell ([req_e e] @
                                             (List.map req_a aa) @
                                             (List.map req_t tt))
        | CellLockAt (c,l,t) -> append Cell [req_c c;req_lv l;req_t t]
        | CellUnlockAt (c,l) -> append Cell [req_c c;req_lv l]
        | CellAt (m,a)       -> append Cell [req_m m;req_a a]

      and req_a (a:addr) : SortSet.t =
        match a with
        | VarAddr _             -> single Addr
        | Null                  -> single Addr
        | NextAt (c,l)          -> append Addr [req_c c;req_lv l]
        | FirstLockedAt (m,p,l) -> append Addr [req_m m;req_p p;req_lv l]

      and req_e (e:elem) : SortSet.t =
        match e with
        | VarElem _         -> single Elem
        | CellData c        -> append Elem [req_c c]
        | HavocSkiplistElem -> single Elem
        | LowestElem        -> single Elem
        | HighestElem       -> single Elem

      and req_t (t:tid) : SortSet.t =
        match t with
        | VarTh _            -> single Thid
        | NoThid             -> single Thid
        | CellLockIdAt (c,l) -> append Thid [req_c c;req_lv l]

      and req_s (s:set) : SortSet.t =
        match s with
        | VarSet _           -> single Set
        | EmptySet           -> single Set
        | Singl a            -> append Set  [req_a a]
        | Union (s1,s2)      -> append Set [req_s s1;req_s s2]
        | Intr (s1,s2)       -> append Set [req_s s1;req_s s2]
        | Setdiff (s1,s2)    -> append Set [req_s s1;req_s s2]
        | PathToSet p        -> append Set [req_p p]
        | AddrToSet (m,a,l)  -> append Set [req_m m;req_a a;req_lv l]

      and req_term (t:term) : SortSet.t =
        match t with
        | VarT (_,s,_,_,_,_)           -> single s
        | SetT s                       -> req_s s
        | ElemT e                      -> req_e e
        | ThidT t                      -> req_t t
        | AddrT a                      -> req_a a
        | CellT c                      -> req_c c
        | SetThT s                     -> req_st s
        | SetElemT s                   -> req_se s
        | PathT p                      -> req_p p
        | MemT m                       -> req_m m
        | LevelT l                     -> req_lv l
        | VarUpdate ((_,s,_,_,_,_),t,tr) -> append s [req_t t;req_term tr]
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
        | Reach (m,a1,a2,l,p) -> append Reachable[ops_m m;ops_a a1;ops_a a2;ops_lv l;ops_p p]
        | OrderList (m,a1,a2) -> append OrderedList[ops_m m;ops_a a1;ops_a a2]
        | In (a,s)            -> list_union [ops_a a;ops_s s]
        | SubsetEq (s1,s2)    -> list_union [ops_s s1;ops_s s2]
        | InTh (t,s)          -> list_union [ops_t t;ops_st s]
        | SubsetEqTh (s1,s2)  -> list_union [ops_st s1;ops_st s2]
        | InElem (e,s)        -> list_union [ops_e e;ops_se s]
        | SubsetEqElem (s1,s2)-> list_union [ops_se s1;ops_se s2]
        | Less (i1,i2)        -> append LevelOrder [ops_lv i1;ops_lv i2]
        | Greater (i1,i2)     -> append LevelOrder [ops_lv i1;ops_lv i2]
        | LessEq (i1,i2)      -> append LevelOrder [ops_lv i1;ops_lv i2]
        | GreaterEq (i1,i2)   -> append LevelOrder [ops_lv i1;ops_lv i2]
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

      and ops_lv (i:level) : OpsSet.t =
        match i with
        | LevelVal _  -> empty
        | VarLevel _  -> empty
        | LevelSucc l -> list_union [ops_lv l]
        | LevelPred l -> list_union [ops_lv l]
        | HavocLevel  -> empty

      and ops_p (p:path) : OpsSet.t =
        match p with
        | VarPath _             -> empty
        | Epsilon               -> empty
        | SimplePath a          -> ops_a a
        | GetPathAt (m,a1,a2,l) -> append Getp [ops_m m;ops_a a1;ops_a a2;ops_lv l]

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
        | MkCell (e,aa,tt)   -> list_union ([ops_e e] @
                                            (List.map ops_a aa) @
                                            (List.map ops_t tt))
        | CellLockAt (c,l,t) -> list_union [ops_c c;ops_lv l;ops_t t]
        | CellUnlockAt (c,l) -> list_union [ops_c c;ops_lv l]
        | CellAt (m,a)       -> list_union [ops_m m;ops_a a]

      and ops_a (a:addr) : OpsSet.t =
        match a with
        | VarAddr _             -> empty
        | Null                  -> empty
        | NextAt (c,l)          -> list_union [ops_c c;ops_lv l]
        | FirstLockedAt (m,p,l) -> append FstLocked [ops_m m;ops_p p;ops_lv l]

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
        | NoThid             -> empty
        | CellLockIdAt (c,l) -> list_union [ops_c c;ops_lv l]

      and ops_s (s:set) : OpsSet.t =
        match s with
        | VarSet _          -> empty
        | EmptySet          -> empty
        | Singl a           -> ops_a a
        | Union (s1,s2)     -> list_union [ops_s s1;ops_s s2]
        | Intr (s1,s2)      -> list_union [ops_s s1;ops_s s2]
        | Setdiff (s1,s2)   -> list_union [ops_s s1;ops_s s2]
        | PathToSet p       -> append Path2Set [ops_p p]
        | AddrToSet (m,a,l) -> append Addr2Set [ops_m m;ops_a a;ops_lv l]

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
        | LevelT i           -> ops_lv i
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


    let conj_list (bs:formula list) : formula =
      match bs with
      | [] -> True
      | x::xs -> List.fold_left (fun a b -> And(a,b)) x xs


    let disj_list (bs:formula list) : formula =
      match bs with
      | [] -> False
      | x::xs -> List.fold_left (fun a b -> Or(a,b)) x xs


    let rec to_conj_list (phi:formula) : formula list =
      match phi with
      | And (f1,f2) -> (to_conj_list f1) @ (to_conj_list f2)
      | _           -> [phi]

    let rec to_disj_list (phi:formula) : formula list =
      match phi with
      | Or (f1,f2) -> (to_disj_list f1) @ (to_disj_list f2)
      | _          -> [phi]


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

    let eq_setelem (s1:setelem) (s2:setelem) : formula =
      Literal (Atom (Eq (SetElemT s1, SetElemT s2)))

    let eq_path (p1:path) (p2:path) : formula =
      Literal (Atom (Eq (PathT p1, PathT p2)))

    let eq_mem (m1:mem) (m2:mem) : formula =
      Literal (Atom (Eq (MemT m1, MemT m2)))

    let eq_level (l1:level) (l2:level) : formula =
      Literal (Atom (Eq (LevelT l1, LevelT l2)))

    let less_level (l1:level) (l2:level) : formula =
      Literal (Atom (Less (l1, l2)))

    let lesseq_level (l1:level) (l2:level) : formula =
      Literal (Atom (LessEq (l1, l2)))

    let greater_level (l1:level) (l2:level) : formula =
      Literal (Atom (Greater (l1, l2)))

    let greatereq_level (l1:level) (l2:level) : formula =
      Literal (Atom (GreaterEq (l1, l2)))

    let eq_term (t1:term) (t2:term) : formula =
      Literal (Atom (Eq (t1, t2)))

    let ineq_set (s1:set) (s2:set) : formula =
      Literal (Atom (InEq (SetT s1, SetT s2)))

    let ineq_elem (e1:elem) (e2:elem) : formula =
      Literal (Atom (InEq (ElemT e1, ElemT e2)))

    let ineq_tid (t1:tid) (t2:tid) : formula =
      Literal (Atom (InEq (ThidT t1, ThidT t2)))

    let ineq_addr (a1:addr) (a2:addr) : formula =
      Literal (Atom (InEq (AddrT a1, AddrT a2)))

    let ineq_cell (c1:cell) (c2:cell) : formula =
      Literal (Atom (InEq (CellT c1, CellT c2)))

    let ineq_setth (s1:setth) (s2:setth) : formula =
      Literal (Atom (InEq (SetThT s1, SetThT s2)))

    let ineq_setelem (s1:setelem) (s2:setelem) : formula =
      Literal (Atom (InEq (SetElemT s1, SetElemT s2)))

    let ineq_path (p1:path) (p2:path) : formula =
      Literal (Atom (InEq (PathT p1, PathT p2)))

    let ineq_mem (m1:mem) (m2:mem) : formula =
      Literal (Atom (InEq (MemT m1, MemT m2)))

    let ineq_level (l1:level) (l2:level) : formula =
      Literal (Atom (InEq (LevelT l1, LevelT l2)))

    let ineq_term (t1:term) (t2:term) : formula =
      Literal (Atom (InEq (t1, t2)))

    let subseteq (s1:set) (s2:set) : formula =
      Literal (Atom (SubsetEq (s1,s2)))

    let atomlit (a:atom) : formula =
      Literal (Atom a)

  end

