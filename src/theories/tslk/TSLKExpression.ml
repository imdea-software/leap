open Printf
open LeapLib

module type S =
  sig

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
      | Level
      | Bool
      | Unknown

    type var_info_t

    module V : Variable.S
      with type sort = sort
      with type info = var_info_t

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
      | LevelT            of level
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
      | AddrToSet         of mem * addr * level
    and tid =
        VarTh             of V.t
      | NoTid
      | CellLockIdAt      of cell * level
    and elem =
        VarElem           of V.t
      | CellData          of cell
      | HavocSkiplistElem
      | LowestElem
      | HighestElem
    and addr =
        VarAddr           of V.t
      | Null
      | NextAt            of cell * level
      | FirstLockedAt     of mem * path * level
    (*  | Malloc of elem * addr * tid *)
    and cell =
        VarCell           of V.t
      | Error
      | MkCell            of elem * addr list * tid list
      | CellLockAt        of cell * level * tid
      | CellUnlockAt      of cell * level
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
      | GetPathAt         of mem * addr * addr * level
    and mem =
        VarMem            of V.t
      | Emp
      | Update            of mem * addr * cell
    and level =
        LevelVal          of int
      | VarLevel          of V.t
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
      | LevelOrder
      | OrderedList


    exception WrongType of term

    (* CALCULATE SET OF VARS *)

    module TermSet : Set.S with type elt = term
    module AtomSet : Set.S with type elt = atom
    module ThreadSet : Set.S with type elt = tid

    (* Expression height *)
    val k : int

    (* Variable construction *)
    val build_var : ?fresh:bool ->
                    ?treat_as_pc:bool ->
                    V.id ->
                    sort ->
                    bool ->
                    V.shared_or_local ->
                    V.procedure_name ->
                    V.t

    (* returns all variables form a formula *)
    val get_varlist_from_conj : conjunctive_formula -> V.t list
    val get_varlist_of_sort_from_conj : conjunctive_formula -> sort -> V.id list
    val varlist_of_sort : V.t list -> sort -> V.id list

    val get_varset_from_literal      : literal -> V.VarSet.t
    val get_varset_from_conj         : conjunctive_formula -> V.VarSet.t
    val get_unparam_varset_from_conj : conjunctive_formula -> V.VarSet.t
    val get_varset_from_formula      : formula -> V.VarSet.t
    val get_unparam_varset_from_formula : formula -> V.VarSet.t
    val get_varset_of_sort_from_conj : conjunctive_formula -> sort -> V.VarSet.t
    val get_termset_from_formula     : formula -> TermSet.t
    val termset_of_sort              : TermSet.t -> sort -> TermSet.t

    val remove_nonparam_local_vars : V.VarSet.t -> V.VarSet.t
    val add_prevstate_local_vars : V.VarSet.t -> V.VarSet.t

    val voc_term : term -> ThreadSet.t
    val voc : formula -> ThreadSet.t
    val conjformula_voc : conjunctive_formula -> ThreadSet.t
    val unprimed_voc : formula -> ThreadSet.t

    val variable_mark_smp_interesting : V.t -> bool -> unit
    val variable_is_smp_interesting : V.t -> bool


    (* SMP MARKING FUNCTIONS *)
    val addr_mark_smp_interesting : addr -> bool -> unit
    val tid_mark_smp_interesting : tid -> bool -> unit

    (* PRETTY_PRINTERS *)
    val variable_to_full_str : V.t -> string
    val atom_to_str     : atom    -> string
    val literal_to_str  : literal -> string
    val conjunctive_formula_to_str : conjunctive_formula -> string
    val disjunctive_formula_to_str : disjunctive_formula -> string
    val term_to_str     : term   -> string
    val addr_to_str     : addr   -> string
    val cell_to_str     : cell   -> string
    val elem_to_str     : elem   -> string
    val tid_to_str      : tid    -> string
    val mem_to_str      : mem    -> string
    val path_to_str     : path   -> string
    val set_to_str      : set    -> string
    val setth_to_str    : setth  -> string
    val formula_to_str  : formula -> string

    (* val eq_to_str      : eq     -> string *)
    (* val diseq_to_str   : diseq  -> string *)

    val sort_to_str : sort -> string
    val info_to_str : var_info_t -> string

    val print_formula : formula -> unit
    val print_conjunctive_formula: conjunctive_formula -> unit
    val print_atom    : atom    -> unit
    val print_literal : literal -> unit
    val print_addr  : addr  -> unit
    val print_cell  : cell  -> unit
    val print_elem  : elem  -> unit
    val print_tid   : tid  -> unit
    val print_mem   : mem   -> unit
    val print_path  : path  -> unit
    val print_set   : set   -> unit
    val print_setth : setth -> unit

    val required_sorts : formula -> sort list
    val special_ops : formula -> special_op_t list

    val get_addrs_eqs_conj : conjunctive_formula -> ((addr*addr) list * (addr*addr) list)
    val get_addrs_eqs : formula -> ((addr*addr) list * (addr*addr) list)

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
      | Level
      | Bool
      | Unknown


    type var_info_t =
      {
        mutable smp_interesting : bool;
        (* CHANGES: Remove the fresh field from here *)
        mutable fresh : bool;
        treat_as_pc : bool;
      }


    module V = Variable.Make (
      struct
        type sort_t = sort
        type info_t = var_info_t
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
      | LevelT            of level
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
      | AddrToSet         of mem * addr * level
    and tid =
        VarTh             of V.t
      | NoTid
      | CellLockIdAt      of cell * level
    and elem =
        VarElem           of V.t
      | CellData          of cell
      | HavocSkiplistElem
      | LowestElem
      | HighestElem
    and addr =
        VarAddr           of V.t
      | Null
      | NextAt            of cell * level
      | FirstLockedAt     of mem * path * level
    (*  | Malloc of elem * addr * tid *)
    and cell =
        VarCell           of V.t
      | Error
      | MkCell            of elem * addr list * tid list
      | CellLockAt        of cell * level * tid
      | CellUnlockAt      of cell * level
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
      | GetPathAt         of mem * addr * addr * level
    and mem =
        VarMem            of V.t
      | Emp
      | Update            of mem * addr * cell
    and level =
        LevelVal          of int
      | VarLevel          of V.t
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
      | LevelOrder
      | OrderedList

    exception WrongType of term


    let k = K.level

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
      V.build id s pr th p
        {smp_interesting = false; fresh = false; treat_as_pc = treat_as_pc; } ~fresh:fresh


    let variable_clean_info (v:V.t) : unit =
      (V.info v).fresh <- false;
      (V.info v).smp_interesting <- false


    let variable_mark_smp_interesting (v:V.t) (b:bool) : unit =
      (V.info v).smp_interesting <- b


    let variable_is_smp_interesting (v:V.t) : bool =
      (V.info v).smp_interesting


    let is_primed_tid (th:tid) : bool =
      match th with
      | VarTh v          -> V.is_primed v
      | NoTid            -> false
      | CellLockIdAt _   -> false
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


    let unify_var_info (info1:var_info_t) (info2:var_info_t) : var_info_t =
      {
        fresh = (info1.fresh || info2.fresh);
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


    let remove_nonparam_local_vars (s:V.VarSet.t) : V.VarSet.t =
      V.VarSet.fold (fun v tmpset ->
        if not (V.is_global v) && V.parameter v = V.Shared then
          tmpset
        else
          V.VarSet.add v tmpset
      ) s V.VarSet.empty


    let unparam_varset (s:V.VarSet.t) : V.VarSet.t =
      V.VarSet.fold (fun v tmpset ->
        V.VarSet.add (V.unparam v) tmpset
      ) s V.VarSet.empty


    let add_prevstate_local_vars (s:V.VarSet.t) : V.VarSet.t =
      V.VarSet.fold (fun v tmpset ->
        let unprime_v = V.unprime v in
        if V.is_primed v && not (V.VarSet.mem unprime_v s) then
          V.VarSet.add v (V.VarSet.add unprime_v tmpset)
        else
          V.VarSet.add v tmpset
      ) s V.VarSet.empty


    let (@@) s1 s2 =
      V.VarSet.union s1 s2

    let get_varset_from_param (v:V.t) : V.VarSet.t =
      match (V.parameter v) with
      | V.Local t -> V.VarSet.singleton t
      | _         -> V.VarSet.empty


    let rec get_varset_set s =
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
                              (get_varset_level l)
    and get_varset_tid th =
      match th with
          VarTh v            -> V.VarSet.singleton v @@ get_varset_from_param v
        | NoTid             -> V.VarSet.empty
        | CellLockIdAt (c,l) -> (get_varset_cell c) @@ (get_varset_level l)
    and get_varset_elem e =
      match e with
          VarElem v         -> V.VarSet.singleton v @@ get_varset_from_param v
        | CellData c        -> get_varset_cell c
        | HavocSkiplistElem -> V.VarSet.empty
        | LowestElem        -> V.VarSet.empty
        | HighestElem       -> V.VarSet.empty
    and get_varset_addr a =
      match a with
          VarAddr v            -> V.VarSet.singleton v @@ get_varset_from_param v
        | Null                 -> V.VarSet.empty
        | NextAt (c,l)         -> (get_varset_cell c) @@ (get_varset_level l)
        | FirstLockedAt(m,p,l) -> (get_varset_mem m) @@ (get_varset_path p) @@
                                  (get_varset_level l)
    (*    | Malloc(e,a,th)   -> (get_varset_elem e) @@ (get_varset_addr a) @@  (get_varset_tid th) *)
    and get_varset_cell c =
      let fold f xs = List.fold_left (fun set x -> (f x) @@ set) V.VarSet.empty xs in
      match c with
          VarCell v           -> V.VarSet.singleton v @@ get_varset_from_param v
        | Error               -> V.VarSet.empty
        | MkCell(e,aa,tt)     -> (get_varset_elem e) @@
                                 (fold get_varset_addr aa) @@
                                 (fold get_varset_tid tt)
        | CellLockAt (c,l,th) -> (get_varset_cell c) @@ (get_varset_level l) @@
                                 (get_varset_tid th)
        | CellUnlockAt (c,l)  -> (get_varset_cell c) @@ (get_varset_level l)
        | CellAt(m,a)         -> (get_varset_mem  m) @@ (get_varset_addr a)
    and get_varset_setth sth =
      match sth with
          VarSetTh v         -> V.VarSet.singleton v @@ get_varset_from_param v
        | EmptySetTh         -> V.VarSet.empty
        | SinglTh(th)        -> (get_varset_tid th)
        | UnionTh(st1,st2)   -> (get_varset_setth st1) @@ (get_varset_setth st2)
        | IntrTh(st1,st2)    -> (get_varset_setth st1) @@ (get_varset_setth st2)
        | SetdiffTh(st1,st2) -> (get_varset_setth st1) @@ (get_varset_setth st2)
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
          VarPath v            -> V.VarSet.singleton v @@ get_varset_from_param v
        | Epsilon              -> V.VarSet.empty
        | SimplePath(a)        -> (get_varset_addr a)
        | GetPathAt(m,a1,a2,l) -> (get_varset_mem m) @@ (get_varset_addr a1) @@
                                  (get_varset_addr a2) @@ (get_varset_level l)
    and get_varset_mem m =
      match m with
          VarMem v           -> V.VarSet.singleton v @@ get_varset_from_param v
        | Emp                -> V.VarSet.empty
        | Update(m,a,c)      -> (get_varset_mem m) @@ (get_varset_addr a) @@ (get_varset_cell c)
    and get_varset_level i =
      match i with
          LevelVal _  -> V.VarSet.empty
        | VarLevel v  -> V.VarSet.singleton v
        | LevelSucc l -> (get_varset_level l)
        | LevelPred l -> (get_varset_level l)
        | HavocLevel  -> V.VarSet.empty
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
        | BoolVar v              -> V.VarSet.singleton v
        | PC(_,th,_)             -> (match th with
                                     | V.Shared -> V.VarSet.empty
                                     | V.Local t -> V.VarSet.singleton t)
        | PCUpdate (_,th)       -> (get_varset_tid th)
        | PCRange(_,_,th,_)     -> (match th with
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
        | LevelT l            -> get_varset_level l
        | VarUpdate(v,_,t)    -> (V.VarSet.singleton v) @@ (get_varset_term t) @@
                                 (get_varset_from_param v)

    let varset_fs = Formula.make_fold
                      Formula.GenericLiteralFold
                      (fun _ a -> get_varset_atom a)
                      (fun _ -> V.VarSet.empty)
                      (@@)

    let get_varset_from_literal (l:literal) : V.VarSet.t =
      unify_varset (Formula.literal_fold varset_fs () l)

    let get_varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
      unify_varset (Formula.conjunctive_formula_fold varset_fs () cf)

    let get_unparam_varset_from_conj (cf:conjunctive_formula) : V.VarSet.t =
      unify_varset (unparam_varset (get_varset_from_conj cf))

    let get_varset_from_formula (phi:formula) : V.VarSet.t =
      unify_varset (Formula.formula_fold varset_fs () phi)

    let get_unparam_varset_from_formula (phi:formula) : V.VarSet.t =
      unify_varset (unparam_varset (get_varset_from_formula phi))

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
      | InTh(th,st)            -> add_list [TidT th; SetThT st]
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

    let get_termset_from_formula (phi:formula) : TermSet.t =
      Formula.formula_fold termset_fs () phi


    let termset_of_sort (all:TermSet.t) (s:sort) : TermSet.t =
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
        | Level     -> (match t with | LevelT _     -> true | _ -> false)
        | Bool      -> (match t with | VarT v       -> (V.sort v) = Bool
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
        | TidT _          -> Tid
        | AddrT _          -> Addr
        | CellT _          -> Cell
        | SetThT _         -> SetTh
        | SetElemT _       -> SetElem
        | PathT _          -> Path
        | MemT _           -> Mem
        | LevelT _         -> Level
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
          VarT(_)        -> true
        | SetT s         -> is_set_flat s
        | ElemT e        -> is_elem_flat   e
        | TidT k        -> is_tid_flat k
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
        | NoTid             -> true
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
    and is_atom_flat (a:atom) : bool =
      match a with
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
      | BoolVar _              -> true
      | PC _                   -> true
      | PCUpdate _             -> true
      | PCRange _              -> true

    let is_flat_fs = Formula.make_fold
                       Formula.GenericLiteralFold
                       (fun _ a -> is_atom_flat a)
                       (fun _ -> true)
                       (&&)

    let is_literal_flat (l:literal) : bool =
      Formula.literal_fold is_flat_fs () l


    (*******************)
    (* PRETTY PRINTERS *)
    (* WIHOUT FOLD     *)
    (*******************)



    let sort_to_str s =
      match s with
          Set       -> "Set"
        | Elem      -> "Elem"
        | Tid      -> "Tid"
        | Addr      -> "Addr"
        | Cell      -> "Cell"
        | SetTh     -> "SetTh"
        | SetElem   -> "SetElem"
        | Path      -> "Path"
        | Mem       -> "Mem"
        | Level     -> "Level"
        | Bool      -> "Bool"
        | Unknown   -> "Unknown"


    let info_to_str (info:var_info_t) : string =
      "SMP Interesting: " ^if info.smp_interesting then "true" else "false"^ "\n" ^
      "Fresh:           " ^if info.fresh then "true" else "false"^ "\n" ^
      "Treat as PC:     " ^if info.treat_as_pc then "true" else "false"^ "\n"


    let rec variable_to_full_str = V.to_full_str sort_to_str info_to_str

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
      | BoolVar v                  -> V.to_str v
      | PC (pc,t,pr)               -> let pc_str = if pr then "pc'" else "pc" in
                                      let th_str = (V.shared_or_local_to_str t) in
                                      Printf.sprintf "%s(%s) = %i" pc_str th_str pc
      | PCUpdate (pc,t)            -> let th_str = tid_to_str t in
                                      Printf.sprintf "pc' = pc{%s<-%i}" th_str pc
      | PCRange (pc1,pc2,t,pr)     -> let pc_str = if pr then "pc'" else "pc" in
                                      let th_str = (V.shared_or_local_to_str t) in
                                      Printf.sprintf "%i <= %s(%s) <= %i"
                                                      pc1 pc_str th_str pc2
    and mem_to_str expr =
      match expr with
          VarMem(v) -> V.to_str v
        | Emp -> Printf.sprintf "emp"
        | Update(mem,add,cell) -> Printf.sprintf "upd(%s,%s,%s)"
            (mem_to_str mem) (addr_to_str add) (cell_to_str cell)
    and level_to_str expr =
      match expr with
          LevelVal n       -> string_of_int n
        | VarLevel v       -> V.to_str v
        | LevelSucc l -> Printf.sprintf "succ (%s)" (level_to_str l)
        | LevelPred l -> Printf.sprintf "pred (%s)" (level_to_str l)
        | HavocLevel     -> Printf.sprintf "havocLevel()"
    and path_to_str expr =
      match expr with
          VarPath(v)                       -> V.to_str v
        | Epsilon                          -> Printf.sprintf "epsilon"
        | SimplePath(addr)                 -> Printf.sprintf "[ %s ]" (addr_to_str addr)
        | GetPathAt(mem,add_from,add_to,l) -> Printf.sprintf "getp(%s,%s,%s,%s)"
                                                (mem_to_str mem)
                                                (addr_to_str add_from)
                                                (addr_to_str add_to)
                                                (level_to_str l)
    and set_to_str e =
      match e with
          VarSet(v)             -> V.to_str v
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
      let concat f xs = String.concat "," (List.map f xs) in
      match e with
          VarCell(v)            -> V.to_str v
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
          VarAddr(v)                -> V.to_str v
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
          VarTh(v)             -> V.to_str v
        | NoTid               -> Printf.sprintf "NoTid"
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
        | LevelT(i)          -> (level_to_str i)
        | VarUpdate (v,th,t) -> let v_str = V.to_str v in
                                let th_str = tid_to_str th in
                                let t_str = term_to_str t in
                                  Printf.sprintf "%s{%s<-%s}" v_str th_str t_str

    and literal_to_str (l:literal) : string =
      Formula.literal_to_str atom_to_str l

    and conjunctive_formula_to_str (cf:conjunctive_formula) : string =
      Formula.conjunctive_formula_to_str atom_to_str cf

    and disjunctive_formula_to_str (df:disjunctive_formula) : string =
      Formula.disjunctive_formula_to_str atom_to_str df

    and formula_to_str (phi:formula) : string =
      Formula.formula_to_str atom_to_str phi

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
      match (V.parameter v) with
      | V.Shared -> ThreadSet.empty
      | V.Local t -> ThreadSet.singleton (VarTh t)


    and voc_term (expr:term) : ThreadSet.t =
      match expr with
        | VarT v             -> (match (V.sort v) with
                                 | Tid -> ThreadSet.singleton (VarTh v)
                                 | _   -> ThreadSet.empty ) @@ get_tid_in v
        | SetT(set)          -> voc_set set
        | AddrT(addr)        -> voc_addr addr
        | ElemT(elem)        -> voc_elem elem
        | TidT(th)           -> voc_tid th
        | CellT(cell)        -> voc_cell cell
        | SetThT(setth)      -> voc_setth setth
        | SetElemT(setelem)  -> voc_setelem setelem
        | PathT(path)        -> voc_path path
        | MemT(mem)          -> voc_mem mem
        | LevelT(i)          -> voc_level i
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
      | AddrToSet(mem,a,l)  -> (voc_mem mem) @@ (voc_addr a) @@ (voc_level l)


    and voc_addr (a:addr) : ThreadSet.t =
      match a with
        VarAddr v                 -> get_tid_in v
      | Null                      -> ThreadSet.empty
      | NextAt(cell,l)            -> (voc_cell cell) @@ (voc_level l)
      | FirstLockedAt(mem,path,l) -> (voc_mem mem) @@ (voc_path path) @@ (voc_level l)


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
      | CellLockIdAt(cell,l) -> (voc_cell cell) @@ (voc_level l)


    and voc_cell (c:cell) : ThreadSet.t =
      let fold f xs = List.fold_left (fun ys x -> (f x) @@ ys) ThreadSet.empty xs in
      match c with
        VarCell v            -> get_tid_in v
      | Error                -> ThreadSet.empty
      | MkCell(data,aa,tt)   -> (voc_elem data)    @@
                                (fold voc_addr aa) @@
                                (fold voc_tid tt)
      | CellLockAt(cell,l,th)-> (voc_cell cell) @@ (voc_level l) @@ (voc_tid th)
      | CellUnlockAt(cell,l) -> (voc_cell cell) @@ (voc_level l)
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
        VarPath v                    -> get_tid_in v
      | Epsilon                      -> ThreadSet.empty
      | SimplePath(addr)             -> (voc_addr addr)
      | GetPathAt(mem,a_from,a_to,l) -> (voc_mem mem) @@
                                        (voc_addr a_from) @@
                                        (voc_addr a_to) @@
                                        (voc_level l)


    and voc_mem (m:mem) : ThreadSet.t =
      match m with
        VarMem v             -> get_tid_in v
      | Emp                  -> ThreadSet.empty
      | Update(mem,add,cell) -> (voc_mem mem) @@ (voc_addr add) @@ (voc_cell cell)


    and voc_level (i:level) : ThreadSet.t =
      match i with
        LevelVal _  -> ThreadSet.empty
      | VarLevel v  -> get_tid_in v
      | LevelSucc l -> voc_level l
      | LevelPred l -> voc_level l
      | HavocLevel  -> ThreadSet.empty


    and voc_atom (a:atom) : ThreadSet.t =
      match a with
        Append(p1,p2,pres)         -> (voc_path p1) @@
                                      (voc_path p2) @@
                                      (voc_path pres)
      | Reach(h,a_from,a_to,l,p)   -> (voc_mem h) @@
                                      (voc_addr a_from) @@
                                      (voc_addr a_to) @@
                                      (voc_level l) @@
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
      | Less (i1,i2)               -> (voc_level i1) @@ (voc_level i2)
      | Greater (i1,i2)            -> (voc_level i1) @@ (voc_level i2)
      | LessEq (i1,i2)             -> (voc_level i1) @@ (voc_level i2)
      | GreaterEq (i1,i2)          -> (voc_level i1) @@ (voc_level i2)
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

    let voc_literal (l:literal) : ThreadSet.t =
      Formula.literal_fold voc_fs () l


    let voc_conjunctive_formula (cf:conjunctive_formula) : ThreadSet.t =
      Formula.conjunctive_formula_fold voc_fs () cf

    let voc_formula (phi:formula) : ThreadSet.t =
      Formula.formula_fold voc_fs () phi


    let voc (phi:formula) : ThreadSet.t =
      voc_formula phi


    let conjformula_voc (cf:conjunctive_formula) : ThreadSet.t =
      voc_conjunctive_formula cf


    let unprimed_voc (phi:formula) : ThreadSet.t =
      ThreadSet.filter (is_primed_tid>>not) (voc phi)



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
        | BoolVar _           -> single Bool
        | PC _                -> single Tid
        | PCUpdate _          -> single Tid
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
        | VarTh _            -> single Tid
        | NoTid             -> single Tid
        | CellLockIdAt (c,l) -> append Tid [req_c c;req_lv l]

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
        | LevelT l                     -> req_lv l
        | VarUpdate (v,t,tr)           -> append (V.sort v) [req_t t;req_term tr] in

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
        | BoolVar _           -> empty
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
        | NoTid             -> empty
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
        | TidT t            -> ops_t t
        | AddrT a            -> ops_a a
        | CellT c            -> ops_c c
        | SetThT s           -> ops_st s
        | SetElemT s         -> ops_se s
        | PathT p            -> ops_p p
        | MemT m             -> ops_m m
        | LevelT i           -> ops_lv i
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

    let eq_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (Eq (LevelT l1, LevelT l2))

    let less_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (Less (l1, l2))

    let lesseq_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (LessEq (l1, l2))

    let greater_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (Greater (l1, l2))

    let greatereq_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (GreaterEq (l1, l2))

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

    let ineq_level (l1:level) (l2:level) : formula =
      Formula.atom_to_formula (InEq (LevelT l1, LevelT l2))

    let ineq_term (t1:term) (t2:term) : formula =
      Formula.atom_to_formula (InEq (t1, t2))

    let subseteq (s1:set) (s2:set) : formula =
      Formula.atom_to_formula (SubsetEq (s1,s2))

    let atomlit (a:atom) : formula =
      Formula.atom_to_formula a

  end

