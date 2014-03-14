open Printf
open LeapLib
open LeapVerbose

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
(*    and formula = atom Formula.formula*)


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
    exception Not_tid_var of tid
    exception UnsupportedTSLKExpr of string
    exception UnsupportedSort of string

    (* CALCULATE SET OF VARS *)

    module TermSet : Set.S with type elt = term
    module AtomSet : Set.S with type elt = atom
    module ThreadSet : Set.S with type elt = tid

    include GenericExpression.S
      with type sort := sort
      with type v_info := var_info_t
      with type tid := tid
      with type atom := atom
      with module V := V
      with module ThreadSet := ThreadSet

    (* Expression height *)
    val k : int

    (* Variable construction *)
    val build_var : ?fresh:bool ->
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

    module E = Expression
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
    exception Not_tid_var of tid
    exception UnsupportedTSLKExpr of string
    exception UnsupportedSort of string


    let k = K.level

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
      V.build id s pr th p {smp_interesting = false; fresh = false; } ~fresh:fresh


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



    (**********  Folding  ***************)

    type ('info, 'a) fold_ops_t =
      {
        base : 'info -> 'a;
        concat : 'a -> 'a -> 'a;
        var_f : ('info,'a) fold_ops_t -> 'info -> V.t -> 'a;
        mutable addr_f : ('info,'a) fold_ops_t -> 'info -> addr -> 'a;
        mutable elem_f : ('info,'a) fold_ops_t -> 'info -> elem -> 'a;
        mutable tid_f : ('info,'a) fold_ops_t -> 'info -> tid -> 'a;
        mutable level_f : ('info,'a) fold_ops_t -> 'info -> level -> 'a;
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
        level_f : 'info -> level -> 'a;
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
      | VarAddr v       -> fs.var_f fs info v
      | Null            -> fs.base info
      | NextAt (c,l)    -> fs.concat (fs.cell_f fs info c)
                                     (fs.level_f fs info l)
      | FirstLockedAt (m,p,l) -> fs.concat (fs.mem_f fs info m)
                                           (fs.concat (fs.path_f fs info p)
                                                      (fs.level_f fs info l))

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
      | CellLockIdAt (c,l) -> fs.concat (fs.cell_f fs info c)
                                        (fs.level_f fs info l)

    and fold_level (fs:('info,'a) fold_ops_t) (info:'info) (l:level) : 'a =
      match l with
      | LevelVal _ -> fs.base info
      | VarLevel v -> fs.var_f fs info v
      | LevelSucc j -> fs.level_f fs info j
      | LevelPred j -> fs.level_f fs info j
      | HavocLevel -> fs.base info

    and fold_cell (fs:('info,'a) fold_ops_t) (info:'info) (c:cell) : 'a =
      match c with
      | VarCell v          -> fs.var_f fs info v
      | Error              -> fs.base info
      | MkCell(e,aa,tt)    -> fs.concat (fs.elem_f fs info e)
                                (fs.concat
                                        (List.fold_left (fun res a ->
                                          fs.concat res (fs.addr_f fs info a)
                                         ) (fs.base info) aa)
                                        (List.fold_left (fun res t ->
                                          fs.concat res (fs.tid_f fs info t)
                                         ) (fs.base info) tt))
      | CellLockAt(c,l,th) -> fs.concat (fs.cell_f fs info c)
                                        (fs.concat (fs.level_f fs info l)
                                                   (fs.tid_f fs info th))
      | CellUnlockAt(c,l)  -> fs.concat (fs.cell_f fs info c) (fs.level_f fs info l)
      | CellAt(m,a)        -> fs.concat (fs.mem_f fs info m) (fs.addr_f fs info a)

    and fold_mem (fs:('info,'a) fold_ops_t) (info:'info) (m:mem) : 'a =
      match m with
      | VarMem v      -> fs.var_f fs info v
      | Emp           -> fs.base info
      | Update(m,a,c) -> fs.concat (fs.mem_f fs info m)
                                   (fs.concat (fs.addr_f fs info a)
                                              (fs.cell_f fs info c))

    and fold_path (fs:('info,'a) fold_ops_t) (info:'info) (p:path) : 'a =
      match p with
      | VarPath v            -> fs.var_f fs info v
      | Epsilon              -> fs.base info
      | SimplePath(a)        -> fs.addr_f fs info a
      | GetPathAt(m,a1,a2,l) -> fs.concat (fs.mem_f fs info m)
                                          (fs.concat (fs.addr_f fs info a1)
                                                     (fs.concat (fs.addr_f fs info a2)
                                                                (fs.level_f fs info l)))

    and fold_set (fs:('info,'a) fold_ops_t) (info:'info) (s:set) : 'a =
      match s with
      | VarSet v         -> fs.var_f fs info v
      | EmptySet         -> fs.base info
      | Singl(a)         -> fs.addr_f fs info a
      | Union(s1,s2)     -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
      | Intr(s1,s2)      -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
      | Setdiff(s1,s2)   -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
      | PathToSet(p)     -> fs.path_f fs info p
      | AddrToSet(m,a,l) -> fs.concat (fs.mem_f fs info m)
                                      (fs.concat (fs.addr_f fs info a)
                                                 (fs.level_f fs info l))

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
      | Append(p1,p2,p3)          -> fs.concat (fs.path_f fs info p1)
                                        (fs.concat (fs.path_f fs info p2)
                                          (fs.path_f fs info p3))
      | Reach(m,a1,a2,l,p)        -> fs.concat (fs.mem_f fs info m)
                                        (fs.concat (fs.addr_f fs info a1)
                                            (fs.concat (fs.addr_f fs info a2)
                                                (fs.concat (fs.level_f fs info l)
                                                    (fs.path_f fs info p))))
      | OrderList(m,a1,a2)        -> fs.concat (fs.mem_f fs info m)
                                        (fs.concat (fs.addr_f fs info a1)
                                            (fs.addr_f fs info a2))
      | In(a,s)                   -> fs.concat (fs.addr_f fs info a) (fs.set_f fs info s)
      | SubsetEq(s1,s2)           -> fs.concat (fs.set_f fs info s1) (fs.set_f fs info s2)
      | InTh(th,st)               -> fs.concat (fs.tid_f fs info th) (fs.setth_f fs info st)
      | SubsetEqTh(st1,st2)       -> fs.concat (fs.setth_f fs info st1)
                                               (fs.setth_f fs info st2)
      | InElem(e,se)              -> fs.concat (fs.elem_f fs info e)
                                               (fs.setelem_f fs info se)
      | SubsetEqElem(se1,se2)     -> fs.concat (fs.setelem_f fs info se1)
                                               (fs.setelem_f fs info se2)
      | Less(l1,l2)               -> fs.concat (fs.level_f fs info l1)
                                               (fs.level_f fs info l2)
      | LessEq(l1,l2)             -> fs.concat (fs.level_f fs info l1)
                                               (fs.level_f fs info l2)
      | Greater(l1,l2)            -> fs.concat (fs.level_f fs info l1)
                                               (fs.level_f fs info l2)
      | GreaterEq(l1,l2)          -> fs.concat (fs.level_f fs info l1)
                                               (fs.level_f fs info l2)
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
      | LevelT l          -> fs.level_f fs info l
      | VarUpdate(v,pc,t) -> fs.concat (fs.var_f fs info v)
                                       (fs.concat (fs.tid_f fs info pc)
                                                  (fs.term_f fs info t))



    let make_fold ?(addr_f=fold_addr)
                  ?(elem_f=fold_elem)
                  ?(tid_f=fold_tid)
                  ?(level_f=fold_level)
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
      let fs = {
        addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
        level_f = level_f; cell_f = cell_f; mem_f = mem_f;
        path_f = path_f; set_f = set_f; setelem_f = setelem_f;
        setth_f = setth_f; atom_f = atom_f; term_f = term_f;
        base = base; concat = concat; var_f = var_f; } in
      { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
        level_f = level_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
        path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
        setth_f = setth_f fs; atom_f = atom_f fs; term_f = term_f fs;
        var_f = var_f fs; }



    (**********  Mapping  ***************)

    type 'info map_ops_t =
      {
        var_f : 'info map_ops_t -> 'info -> V.t -> V.t;
        mutable addr_f : 'info map_ops_t -> 'info -> addr -> addr;
        mutable elem_f : 'info map_ops_t -> 'info -> elem -> elem;
        mutable tid_f : 'info map_ops_t -> 'info -> tid -> tid;
        mutable level_f : 'info map_ops_t -> 'info -> level -> level;
        mutable cell_f : 'info map_ops_t -> 'info -> cell -> cell;
        mutable mem_f : 'info map_ops_t -> 'info -> mem -> mem;
        mutable path_f : 'info map_ops_t -> 'info -> path -> path;
        mutable set_f : 'info map_ops_t -> 'info -> set -> set;
        mutable setelem_f : 'info map_ops_t -> 'info -> setelem -> setelem;
        mutable setth_f : 'info map_ops_t -> 'info -> setth -> setth;
        mutable atom_f : 'info map_ops_t -> 'info -> atom -> atom;
        mutable term_f : 'info map_ops_t -> 'info -> term -> term;
      }

    type 'info mapping_t =
      {
        var_f : 'info -> V.t -> V.t;
        addr_f : 'info -> addr -> addr;
        elem_f : 'info -> elem -> elem;
        tid_f : 'info -> tid -> tid;
        level_f : 'info -> level -> level;
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
      | VarAddr v             -> VarAddr (fs.var_f fs info v)
      | Null                  -> Null
      | NextAt (c,l)          -> NextAt (fs.cell_f fs info c, fs.level_f fs info l)
      | FirstLockedAt (m,p,l) -> FirstLockedAt (fs.mem_f fs info m,
                                                fs.path_f fs info p,
                                                fs.level_f fs info l)

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
      | CellLockIdAt (c,l) -> CellLockIdAt (fs.cell_f fs info c,
                                            fs.level_f fs info l)

    and map_level (fs:'info map_ops_t) (info:'info) (l:level) : level =
      match l with
      | LevelVal i  -> LevelVal i
      | VarLevel v  -> VarLevel (fs.var_f fs info v)
      | LevelSucc j -> LevelSucc (fs.level_f fs info j)
      | LevelPred j -> LevelPred (fs.level_f fs info j)
      | HavocLevel  -> HavocLevel

    and map_cell (fs:'info map_ops_t) (info:'info) (c:cell) : cell =
      match c with
      | VarCell v          -> VarCell (fs.var_f fs info v)
      | Error              -> Error
      | MkCell(e,aa,tt)    -> MkCell (fs.elem_f fs info e,
                                      List.map (fs.addr_f fs info) aa,
                                      List.map (fs.tid_f fs info) tt)
      | CellLockAt(c,l,th) -> CellLockAt(fs.cell_f fs info c,
                                         fs.level_f fs info l,
                                         fs.tid_f fs info th)
      | CellUnlockAt(c,l)  -> CellUnlockAt (fs.cell_f fs info c, fs.level_f fs info l)
      | CellAt(m,a)        -> CellAt (fs.mem_f fs info m, fs.addr_f fs info a)

    and map_mem (fs:'info map_ops_t) (info:'info) (m:mem) : mem =
      match m with
      | VarMem v      -> VarMem (fs.var_f fs info v)
      | Emp           -> Emp
      | Update(m,a,c) -> Update (fs.mem_f fs info m,
                                 fs.addr_f fs info a,
                                 fs.cell_f fs info c)

    and map_path (fs:'info map_ops_t) (info:'info) (p:path) : path =
      match p with
      | VarPath v            -> VarPath (fs.var_f fs info v)
      | Epsilon              -> Epsilon
      | SimplePath(a)        -> SimplePath (fs.addr_f fs info a)
      | GetPathAt(m,a1,a2,l) -> GetPathAt (fs.mem_f fs info m,
                                           fs.addr_f fs info a1,
                                           fs.addr_f fs info a2,
                                           fs.level_f fs info l)

    and map_set (fs:'info map_ops_t) (info:'info) (s:set) : set =
      match s with
      | VarSet v         -> VarSet (fs.var_f fs info v)
      | EmptySet         -> EmptySet
      | Singl(a)         -> Singl (fs.addr_f fs info a)
      | Union(s1,s2)     -> Union (fs.set_f fs info s1, fs.set_f fs info s2)
      | Intr(s1,s2)      -> Intr (fs.set_f fs info s1, fs.set_f fs info s2)
      | Setdiff(s1,s2)   -> Setdiff (fs.set_f fs info s1, fs.set_f fs info s2)
      | PathToSet(p)     -> PathToSet (fs.path_f fs info p)
      | AddrToSet(m,a,l) -> AddrToSet (fs.mem_f fs info m,
                                       fs.addr_f fs info a,
                                       fs.level_f fs info l)

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

    and map_atom (fs:'info map_ops_t) (info:'info) (a:atom) : atom =
      match a with
      | Append(p1,p2,p3)          -> Append (fs.path_f fs info p1,
                                             fs.path_f fs info p2,
                                             fs.path_f fs info p3)
      | Reach(m,a1,a2,l,p)        -> Reach (fs.mem_f fs info m,
                                            fs.addr_f fs info a1,
                                            fs.addr_f fs info a2,
                                            fs.level_f fs info l,
                                            fs.path_f fs info p)
      | OrderList(m,a1,a2)        -> OrderList (fs.mem_f fs info m,
                                                fs.addr_f fs info a1,
                                                fs.addr_f fs info a2)
      | In(a,s)                   -> In (fs.addr_f fs info a, fs.set_f fs info s)
      | SubsetEq(s1,s2)           -> SubsetEq (fs.set_f fs info s1,
                                               fs.set_f fs info s2)
      | InTh(th,st)               -> InTh (fs.tid_f fs info th, fs.setth_f fs info st)
      | SubsetEqTh(st1,st2)       -> SubsetEqTh (fs.setth_f fs info st1,
                                                 fs.setth_f fs info st2)
      | InElem(e,se)              -> InElem (fs.elem_f fs info e,
                                             fs.setelem_f fs info se)
      | SubsetEqElem(se1,se2)     -> SubsetEqElem (fs.setelem_f fs info se1,
                                                   fs.setelem_f fs info se2)
      | Less(l1,l2)               -> Less (fs.level_f fs info l1,
                                           fs.level_f fs info l2)
      | LessEq(l1,l2)             -> LessEq (fs.level_f fs info l1,
                                             fs.level_f fs info l2)
      | Greater(l1,l2)            -> Greater (fs.level_f fs info l1,
                                              fs.level_f fs info l2)
      | GreaterEq(l1,l2)          -> GreaterEq (fs.level_f fs info l1,
                                                fs.level_f fs info l2)
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
      | LevelT l          -> LevelT (fs.level_f fs info l)
      | VarUpdate(v,pc,t) -> VarUpdate (fs.var_f fs info v,
                                        fs.tid_f fs info pc,
                                        fs.term_f fs info t)



    let make_map ?(addr_f=map_addr)
                 ?(elem_f=map_elem)
                 ?(tid_f=map_tid)
                 ?(level_f=map_level)
                 ?(cell_f=map_cell)
                 ?(mem_f=map_mem)
                 ?(path_f=map_path)
                 ?(set_f=map_set)
                 ?(setelem_f=map_setelem)
                 ?(setth_f=map_setth)
                 ?(atom_f=map_atom)
                 ?(term_f=map_term)
                 (var_f :('info map_ops_t -> 'info -> V.t -> V.t))
        : 'info mapping_t =
      let fs : 'info map_ops_t = {
        addr_f = addr_f; elem_f = elem_f; tid_f = tid_f;
        level_f = level_f; cell_f = cell_f; mem_f = mem_f;
        path_f = path_f; set_f = set_f; setelem_f = setelem_f;
        setth_f = setth_f; atom_f = atom_f; term_f = term_f;
        var_f = var_f; } in
      { addr_f = addr_f fs; elem_f = elem_f fs; tid_f = tid_f fs;
        level_f = level_f fs; cell_f = cell_f fs; mem_f = mem_f fs;
        path_f = path_f fs; set_f = set_f fs; setelem_f = setelem_f fs;
        setth_f = setth_f fs; atom_f = atom_f fs; term_f = term_f fs;
        var_f = var_f fs; }




    let unify_var_info (info1:var_info_t) (info2:var_info_t) : var_info_t =
      {
        fresh = (info1.fresh || info2.fresh);
        smp_interesting = (info1.smp_interesting || info2.smp_interesting);
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
      Hashtbl.fold (fun (id,s,pr,th,p) info set ->
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




    let get_varset_from_param (v:V.t) : V.VarSet.t =
      match (V.parameter v) with
      | V.Local t -> V.VarSet.singleton t
      | _         -> V.VarSet.empty

    let varset_fold =
      make_fold (fun _ -> V.VarSet.empty) V.VarSet.union
                (fun _ _ v -> V.VarSet.union (V.VarSet.singleton v)
                                             (get_varset_from_param v))

    let varset_fs = Formula.make_fold
                      Formula.GenericLiteralFold
                      (varset_fold.atom_f)
                      (fun info -> V.VarSet.empty)
                      (V.VarSet.union)

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
      | PC(pc,th,pr)           -> (match th with
                                   | V.Shared  -> TermSet.empty
                                   | V.Local t -> add_list [TidT (VarTh t)])
      | PCUpdate (pc,th)       -> add_list [TidT th]
      | PCRange(pc1,pc2,th,pr) -> (match th with
                                   | V.Shared  -> TermSet.empty
                                   | V.Local t -> add_list [TidT (VarTh t)])

    let termset_fs = Formula.make_fold
                       Formula.GenericLiteralFold
                       (fun info a -> get_termset_atom a)
                       (fun info -> TermSet.empty)
                       TermSet.union

    let get_termset_from_formula (phi:formula) : TermSet.t =
      Formula.formula_fold termset_fs () phi


    let termset_of_sort (all:TermSet.t) (s:sort) : TermSet.t =
      let match_sort (t:term) : bool =
        match s with
        | Set       -> (match t with | SetT _       -> true | _ -> false)
        | Elem      -> (match t with | ElemT _      -> true | _ -> false)
        | Tid       -> (match t with | TidT _       -> true | _ -> false)
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

    let is_var_fold =
      make_fold (fun _ -> false) (fun _ _ -> false) (fun _ _ _ -> true)


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
        | LevelT _         -> Level
        | VarUpdate(v,_,_) -> (V.sort v)
      
    let terms_same_type a b =
      (get_sort_from_term a) = (get_sort_from_term b)



    let is_flat_fold =
      make_fold (fun _ -> true) (&&) (fun _ _ _ -> true)
      ~atom_f:(fun fs info a -> match a with
                                | BoolVar _
                                | PC _
                                | PCUpdate _
                                | PCRange _ -> true
                                | _ -> fold_atom fs info a)


    let is_flat_fs = Formula.make_fold
                       Formula.GenericLiteralFold
                       (is_flat_fold.atom_f)
                       (fun info -> true)
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
      "Fresh:           " ^if info.fresh then "true" else "false"^ "\n"


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
    let rec get_tid_in (v:V.t) : ThreadSet.t =
      match (V.parameter v) with
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

    let voc_fs = Formula.make_fold
                   Formula.GenericLiteralFold
                   (voc_fold.atom_f)
                   (fun info -> ThreadSet.empty)
                   (ThreadSet.union)

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
      let req_fold =
        make_fold (fun _ -> SortSet.empty) SortSet.union
                  (fun _ _ _ -> SortSet.empty)
        ~atom_f:(fun fs info a ->
            match a with
            | BoolVar _ -> SortSet.singleton Bool
            | PC _ -> SortSet.singleton Tid
            | PCUpdate _ -> SortSet.singleton Tid
            | PCRange _ -> SortSet.empty
            | _ -> fold_atom fs info a)
        ~mem_f:(fun fs info m ->
            SortSet.add Mem (fold_mem fs info m))
        ~level_f:(fun fs info l ->
            match l with
            | HavocLevel -> SortSet.empty
            | _ -> SortSet.add Level (fold_level fs info l))
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


      let req_fs = Formula.make_fold
                     Formula.GenericLiteralFold
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
            | Less _
            | Greater _
            | LessEq _
            | GreaterEq _ -> OpsSet.add LevelOrder (fold_atom fs info a)
            | LessElem _ -> OpsSet.add ElemOrder (fold_atom fs info a)
            | GreaterElem _ -> OpsSet.add ElemOrder (fold_atom fs info a)
            | BoolVar _
            | PC _
            | PCUpdate _
            | PCRange _ -> OpsSet.empty
            | _ -> fold_atom fs info a)
        ~addr_f:(fun fs info a ->
          match a with
          | FirstLockedAt _ -> OpsSet.add FstLocked (fold_addr fs info a)
          | _ -> fold_addr fs info a)
        ~path_f:(fun fs info p ->
          match p with
          | GetPathAt _ -> OpsSet.add Getp (fold_path fs info p)
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


      let ops_fs = Formula.make_fold
                     Formula.GenericLiteralFold
                     (ops_fold.atom_f)
                     (fun info -> OpsSet.empty)
                     OpsSet.union

      in
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


    (* Vocabulary to variable conversion *)
    let voc_to_var (t:tid) : V.t =
      match t with
      | VarTh v -> v
      | _ -> raise(Not_tid_var t)

    let param_map =
      make_map (fun _ pfun v -> V.set_param v (pfun (Some v)))

    let param_fs =
      F.make_trans F.GenericLiteralTrans param_map.atom_f

    (*********************  Expression to TSLK Expression  ********************)


    (* Machinery for array conversion *)
    let addrarr_tbl : (E.addrarr, addr list) Hashtbl.t = Hashtbl.create 10


    let rec expand_array_to_var (v:E.V.t)
                            (s:sort)
                            (n:int) : V.t =
      let id_str = E.V.id v in
      let pr_str = if E.V.is_primed v then "_prime" else "" in
      let th_str = match E.V.parameter v with
                   | E.V.Shared -> ""
                   | E.V.Local t -> "_" ^ (E.V.to_str t) in
      let p_str = match E.V.scope v with
                  | E.V.GlobalScope -> ""
                  | E.V.Scope p -> p ^ "_" in
      let new_id = p_str ^ id_str ^ th_str ^ pr_str ^ "__" ^ (string_of_int n) in
      let v_fresh = build_var new_id s false V.Shared V.GlobalScope ~fresh:true in
      verbl _LONG_INFO "FRESH VAR: %s\n" new_id;
      v_fresh


    and gen_addr_list (aa:E.addrarr) : addr list =
      let xs = ref [] in
      for n = (k - 1) downto 0 do
        let v = match aa with
                | E.VarAddrArray v ->
                    VarAddr (expand_array_to_var v Addr n)
                | E.CellArr c -> raise(UnsupportedTSLKExpr(E.addrarr_to_str aa))
                | _ -> Null in
        xs := v::(!xs)
      done;
      verbl _LONG_INFO "**** TSL Solver, generated address list for %s: [%s]\n"
              (E.addrarr_to_str aa)
              (String.concat ";" (List.map addr_to_str !xs));
      !xs


    and get_addr_list (aa:E.addrarr) : addr list =
      try
        Hashtbl.find addrarr_tbl aa
      with _ -> begin
        let aa' = gen_addr_list aa in
        Hashtbl.add addrarr_tbl aa aa'; aa'
      end


    let rec sort_to_tslk_sort (s:E.sort) : sort =
      match s with
        E.Set       -> Set
      | E.Elem      -> Elem
      | E.Tid      -> Tid
      | E.Addr      -> Addr
      | E.Cell      -> Cell
      | E.SetTh     -> SetTh
      | E.SetElem   -> SetElem
      | E.Path      -> Path
      | E.Mem       -> Mem
      | E.Bool      -> Bool
      | E.Int       -> Level
      | E.Unknown   -> Unknown
      | _           -> raise(UnsupportedSort(E.sort_to_str s))


    and build_term_var (v:E.V.t) : term =
      let tslk_v = var_to_tslk_var v in
      match (E.V.sort v) with
        E.Set       -> SetT       (VarSet        tslk_v)
      | E.Elem      -> ElemT      (VarElem       tslk_v)
      | E.Tid       -> TidT       (VarTh         tslk_v)
      | E.Addr      -> AddrT      (VarAddr       tslk_v)
      | E.Cell      -> CellT      (VarCell       tslk_v)
      | E.SetTh     -> SetThT     (VarSetTh      tslk_v)
      | E.Path      -> PathT      (VarPath       tslk_v)
      | E.Mem       -> MemT       (VarMem        tslk_v)
      | E.Int       -> LevelT     (VarLevel      tslk_v)
      | _           -> VarT       (tslk_v)



    and var_to_tslk_var (v:E.V.t) : V.t =
      build_var (E.V.id v)
                    (sort_to_tslk_sort (E.V.sort v))
                    (E.V.is_primed v)
                    (shared_to_tslk_shared (E.V.parameter v))
                    (scope_to_tslk_scope (E.V.scope v))


    and shared_to_tslk_shared (th:E.V.shared_or_local) : V.shared_or_local =
      match th with
      | E.V.Shared -> V.Shared
      | E.V.Local t -> V.Local (var_to_tslk_var t)


    and scope_to_tslk_scope (p:E.V.procedure_name) : V.procedure_name =
      match p with
      | E.V.GlobalScope -> V.GlobalScope
      | E.V.Scope proc -> V.Scope proc


    and tid_to_tslk_tid (th:E.tid) : tid =
      match th with
        E.VarTh v            -> VarTh (var_to_tslk_var v)
      | E.NoTid              -> NoTid
      | E.CellLockIdAt (c,l) -> CellLockIdAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l)
      | _                    -> raise(UnsupportedTSLKExpr(E.tid_to_str th))

    and term_to_tslk_term (t:E.term) : term =
      match t with
        E.VarT v        -> VarT (var_to_tslk_var v)
      | E.SetT s        -> SetT (set_to_tslk_set s)
      | E.ElemT e       -> ElemT (elem_to_tslk_elem e)
      | E.TidT t        -> TidT (tid_to_tslk_tid t)
      | E.AddrT a       -> AddrT (addr_to_tslk_addr a)
      | E.CellT c       -> CellT (cell_to_tslk_cell c)
      | E.SetThT st     -> SetThT (setth_to_tslk_setth st)
      | E.SetElemT st   -> SetElemT (setelem_to_tslk_setelem st)
      | E.PathT p       -> PathT (path_to_tslk_path p)
      | E.MemT m        -> MemT (mem_to_tslk_mem m)
      | E.IntT i        -> LevelT (int_to_tslk_level i)
      | E.ArrayT a      -> arrays_to_tslk_term a
      | _               -> raise(UnsupportedTSLKExpr(E.term_to_str t))


    and arrays_to_tslk_term (a:E.arrays) : term =
      match a with
      | E.VarArray v -> build_term_var v
      | E.ArrayUp (E.VarArray v,th_p,E.Term t) ->
          let tslk_v  = var_to_tslk_var v in
          let tslk_th = tid_to_tslk_tid th_p in
          let tslk_t  = term_to_tslk_term t
          in
            VarUpdate (tslk_v, tslk_th, tslk_t)
      | _ -> raise(UnsupportedTSLKExpr(E.arrays_to_str a))


    and set_to_tslk_set (s:E.set) : set =
      let to_set = set_to_tslk_set in
      match s with
        E.VarSet v            -> VarSet (var_to_tslk_var v)
      | E.EmptySet            -> EmptySet
      | E.Singl a             -> Singl (addr_to_tslk_addr a)
      | E.Union (s1,s2)       -> Union (to_set s1, to_set s2)
      | E.Intr (s1,s2)        -> Intr (to_set s1, to_set s2)
      | E.Setdiff (s1,s2)     -> Setdiff (to_set s1, to_set s2)
      | E.PathToSet p         -> PathToSet (path_to_tslk_path p)
      | E.AddrToSetAt (m,a,l) -> AddrToSet (mem_to_tslk_mem m,
                                                    addr_to_tslk_addr a,
                                                    int_to_tslk_level l)
      | E.SetArrayRd (E.VarArray v,t) ->
          VarSet (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _                     -> raise(UnsupportedTSLKExpr(E.set_to_str s))


    and elem_to_tslk_elem (e:E.elem) : elem =
      match e with
        E.VarElem v              -> VarElem (var_to_tslk_var v)
      | E.CellData c             -> CellData (cell_to_tslk_cell c)
      | E.ElemArrayRd (E.VarArray v,t) ->
          VarElem (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | E.HavocSkiplistElem      -> HavocSkiplistElem
      | E.LowestElem             -> LowestElem
      | E.HighestElem            -> HighestElem
      | _                        -> raise(UnsupportedTSLKExpr(E.elem_to_str e))


    and addr_to_tslk_addr (a:E.addr) : addr =
      match a with
        E.VarAddr v              -> VarAddr (var_to_tslk_var v)
      | E.Null                   -> Null
      | E.NextAt (c,l)           -> NextAt (cell_to_tslk_cell c, int_to_tslk_level l)
      | E.FirstLockedAt (m,p,l)  -> FirstLockedAt (mem_to_tslk_mem m,
                                                          path_to_tslk_path p,
                                                          int_to_tslk_level l)
      | E.AddrArrayRd (E.VarArray v,t) ->
          VarAddr (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _                        -> raise(UnsupportedTSLKExpr(E.addr_to_str a))


    and cell_to_tslk_cell (c:E.cell) : cell =
      match c with
        E.VarCell v            -> VarCell (var_to_tslk_var v)
      | E.Error                -> Error
      | E.MkSLKCell (e,aa,tt)  ->
          if List.length aa > k || List.length tt > k then
            begin
              Interface.Err.msg "Too many addresses or threads ids in MkCell" $
                Printf.sprintf "Tried to build a term:\n%s\n while in TSLK[%i]. \
                                Notice the number of addresses or threads identifiers \
                                exceeds the parameter of the theory."
                                (E.cell_to_str c) k;
              raise(UnsupportedTSLKExpr(E.cell_to_str c))
            end
          else
            let aa_pad = LeapLib.list_of (k - List.length aa) Null in
            let tt_pad = LeapLib.list_of (k - List.length tt) NoTid in
            MkCell (elem_to_tslk_elem e,
                         (List.map addr_to_tslk_addr aa) @ aa_pad,
                         (List.map tid_to_tslk_tid tt) @ tt_pad)
      (* TSLK receives two arguments, while current epxression receives only one *)
      (* However, for the list examples, I think we will not need it *)
      | E.CellLockAt (c,l,t)   -> CellLockAt (cell_to_tslk_cell c,
                                                     int_to_tslk_level l,
                                                     tid_to_tslk_tid t)
      | E.CellUnlockAt (c,l)   -> CellUnlockAt (cell_to_tslk_cell c,
                                                       int_to_tslk_level l)
      | E.CellAt (m,a)         -> CellAt (mem_to_tslk_mem m, addr_to_tslk_addr a)
      | E.CellArrayRd (E.VarArray v,t) ->
          VarCell (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _ -> raise(UnsupportedTSLKExpr(E.cell_to_str c))


    and setth_to_tslk_setth (st:E.setth) : setth =
      let to_setth = setth_to_tslk_setth in
      match st with
        E.VarSetTh v        -> VarSetTh (var_to_tslk_var v)
      | E.EmptySetTh        -> EmptySetTh
      | E.SinglTh t         -> SinglTh (tid_to_tslk_tid t)
      | E.UnionTh (s1,s2)   -> UnionTh (to_setth s1, to_setth s2)
      | E.IntrTh (s1,s2)    -> IntrTh (to_setth s1, to_setth s2)
      | E.SetdiffTh (s1,s2) -> SetdiffTh (to_setth s1, to_setth s2)
      | E.SetThArrayRd (E.VarArray v,t) ->
          VarSetTh (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _                   -> raise(UnsupportedTSLKExpr(E.setth_to_str st))


    and setelem_to_tslk_setelem (st:E.setelem) : setelem =
      let to_setelem = setelem_to_tslk_setelem in
      match st with
        E.VarSetElem v        -> VarSetElem (var_to_tslk_var v)
      | E.EmptySetElem        -> EmptySetElem
      | E.SinglElem e         -> SinglElem (elem_to_tslk_elem e)
      | E.UnionElem (s1,s2)   -> UnionElem (to_setelem s1, to_setelem s2)
      | E.IntrElem (s1,s2)    -> IntrElem (to_setelem s1, to_setelem s2)
      | E.SetdiffElem (s1,s2) -> SetdiffElem (to_setelem s1, to_setelem s2)
      | E.SetElemArrayRd (E.VarArray v,t) ->
          VarSetElem (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | E.SetToElems (s,m)    -> SetToElems (set_to_tslk_set s,
                                                    mem_to_tslk_mem m)
      | _                     -> raise(UnsupportedTSLKExpr(E.setelem_to_str st))


    and path_to_tslk_path (p:E.path) : path =
      match p with
        E.VarPath v             -> VarPath (var_to_tslk_var v)
      | E.Epsilon               -> Epsilon
      | E.SimplePath a          -> SimplePath (addr_to_tslk_addr a)
      | E.GetPathAt (m,a1,a2,l) -> GetPathAt (mem_to_tslk_mem m,
                                                      addr_to_tslk_addr a1,
                                                      addr_to_tslk_addr a2,
                                                      int_to_tslk_level l)
      | E.PathArrayRd (E.VarArray v,t) ->
          VarPath (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _ -> raise(UnsupportedTSLKExpr(E.path_to_str p))


    and mem_to_tslk_mem (m:E.mem) : mem =
      match m with
        E.VarMem v       -> VarMem (var_to_tslk_var v)
      | E.Update (m,a,c) -> Update (mem_to_tslk_mem m,
                                           addr_to_tslk_addr a,
                                           cell_to_tslk_cell c)
      (* Missing the case for "emp" *)
      | E.MemArrayRd (E.VarArray v,t) ->
          VarMem (var_to_tslk_var (E.V.set_param v (E.V.Local (E.voc_to_var t))))
      | _ -> raise(UnsupportedTSLKExpr(E.mem_to_str m))


    and int_to_tslk_level (i:E.integer) : level =
      let rec apply n f x = if n <= 1 then f x else apply (n-1) f (f x) in
      let succ = (fun x -> LevelSucc x) in
      let pred = (fun x -> LevelPred x) in
      let tolevel = int_to_tslk_level in
      match i with
        E.IntVal l       -> (*if l < 0 || k <= l then
                                 begin
                                   Interface.Err.msg "Level out of bounds" $
                                   Printf.sprintf "Level %i is out of the bounds of TSLK[%i], \
                                                   which goes from 0 to %i."
                                      l k (k-1);
                                   raise(UnsupportedTSLKExpr(E.integer_to_str i))
                                 end
                               else *)
                                 LevelVal l
      | E.VarInt v       -> VarLevel (var_to_tslk_var v)
      | E.IntAdd (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (E.IntVal j1, E.IntVal j2) -> LevelVal (j1+j2)
                                 | (E.VarInt v , E.IntVal j ) -> apply j succ (tolevel i1)
                                 | (E.IntVal j , E.VarInt v ) -> apply j succ (tolevel i2)
                                 | _ -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
                               end
      | E.IntSub (i1,i2) -> begin
                                 match (i1,i2) with
                                 | (E.IntVal j1, E.IntVal j2) -> LevelVal (j1-j2)
                                 | (E.VarInt v , E.IntVal j ) -> apply j pred (tolevel i1)
                                 | _ -> raise(UnsupportedTSLKExpr(E.integer_to_str i))
                               end
      | E.CellMax (c)    -> LevelVal k
      | E.HavocLevel     -> HavocLevel
      | _                -> raise(UnsupportedTSLKExpr(E.integer_to_str i))


    and atom_to_tslk_atom (a:E.atom) : atom =
      let path    = path_to_tslk_path       in
      let mem     = mem_to_tslk_mem         in
      let addr    = addr_to_tslk_addr       in
      let elem    = elem_to_tslk_elem       in
      let set     = set_to_tslk_set         in
      let tid     = tid_to_tslk_tid         in
      let setth   = setth_to_tslk_setth     in
      let setelem = setelem_to_tslk_setelem in
      let integ   = int_to_tslk_level       in
      let term    = term_to_tslk_term       in
      match a with
        E.Append (p1,p2,p3)    -> Append (path p1,path p2,path p3)
      | E.ReachAt (m,a1,a2,l,p)-> Reach (mem m, addr a1, addr a2, integ l, path p)
      | E.OrderList(m,a1,a2)   -> OrderList (mem m, addr a1, addr a2)
      | E.In (a,s)             -> In (addr a, set s)
      | E.SubsetEq (s1,s2)     -> SubsetEq (set s1, set s2)
      | E.InTh (t,s)           -> InTh (tid t, setth s)
      | E.SubsetEqTh (s1,s2)   -> SubsetEqTh (setth s1, setth s2)
      | E.InElem (e,s)         -> InElem (elem_to_tslk_elem e, setelem s)
      | E.SubsetEqElem (s1,s2) -> SubsetEqElem (setelem s1, setelem s2)
      | E.Less (i1,i2)         -> Less (integ i1, integ i2)
      | E.Greater (i1,i2)      -> Greater (integ i1, integ i2)
      | E.LessEq (i1,i2)       -> LessEq (integ i1, integ i2)
      | E.GreaterEq (i1,i2)    -> GreaterEq (integ i1, integ i2)
      | E.LessElem (e1,e2)     -> LessElem (elem e1, elem e2)
      | E.GreaterElem (e1,e2)  -> GreaterElem (elem e1, elem e2)
      | E.Eq (t1,t2)           -> Eq (term t1, term t2)
      | E.InEq (t1,t2)         -> InEq (term t1, term t2)
      | E.BoolVar v            -> BoolVar (var_to_tslk_var v)
      | E.PC (pc,t,pr)         -> PC (pc, shared_to_tslk_shared t,pr)
      | E.PCUpdate (pc,t)      -> PCUpdate (pc, tid_to_tslk_tid t)
      | E.PCRange (pc1,pc2,t,pr) -> PCRange (pc1, pc2, shared_to_tslk_shared t, pr)
      | _                      -> raise(UnsupportedTSLKExpr(E.atom_to_str a))


    and literal_to_tslk_literal (l:E.literal) : literal =
      match l with
        F.Atom a    -> F.Atom (atom_to_tslk_atom a)
      | F.NegAtom a -> F.NegAtom (atom_to_tslk_atom a)


    and formula_to_tslk_formula (f:E.formula) : formula =
(*      LOG "Entering formula_to_tslk_formula..." LEVEL TRACE; *)
      let to_formula = formula_to_tslk_formula in
      match f with
      (* Translation of literals of the form B = A {l <- a} *)
      | F.Literal(F.Atom(E.Eq(E.AddrArrayT(E.VarAddrArray _ as bb),E.AddrArrayT(E.AddrArrayUp(aa,l,a)))))
      | F.Literal(F.Atom(E.Eq(E.AddrArrayT(E.AddrArrayUp(aa,l,a)),E.AddrArrayT(E.VarAddrArray _ as bb))))
      | F.Literal(F.NegAtom(E.InEq(E.AddrArrayT(E.VarAddrArray _ as bb),E.AddrArrayT(E.AddrArrayUp(aa,l,a)))))
      | F.Literal(F.NegAtom(E.InEq(E.AddrArrayT(E.AddrArrayUp(aa,l,a)),E.AddrArrayT(E.VarAddrArray _ as bb)))) ->
          begin
            let a' = addr_to_tslk_addr a in
            let l' = int_to_tslk_level l in
            let aa' = get_addr_list aa in
            let bb' = get_addr_list bb in
            let xs = ref [] in
            for n = 0 to (k - 1) do
              let n' = LevelVal n in
              xs := (F.Implies
                      (eq_level l' n',
                       eq_addr a' (List.nth bb' n))) ::
                    (F.Implies
                      (ineq_level l' n',
                       eq_addr (List.nth aa' n) (List.nth bb' n))) ::
                    (!xs)
            done;
            addr_mark_smp_interesting a' true;
            F.conj_list (!xs)
          end
      (* Translation of literals of the form a = A[i] *)
      | F.Literal(F.Atom(E.Eq(E.AddrT a,E.AddrT(E.AddrArrRd(aa,i)))))
      | F.Literal(F.Atom(E.Eq(E.AddrT(E.AddrArrRd(aa,i)),E.AddrT a)))
      | F.Literal(F.NegAtom(E.InEq(E.AddrT a,E.AddrT(E.AddrArrRd(aa,i)))))
      | F.Literal(F.NegAtom(E.InEq(E.AddrT(E.AddrArrRd(aa,i)),E.AddrT a))) ->
          let a' = addr_to_tslk_addr a in
          let aa' = get_addr_list aa in
          let i' = int_to_tslk_level i in
          let xs = ref [] in
          for n = 0 to (k - 1) do
            let n' = LevelVal n in
            xs := (F.Implies
                    (eq_level i' n',
                     eq_addr a' (List.nth aa' n))) :: (!xs)
          done;
          addr_mark_smp_interesting a' true;
          F.conj_list (!xs)
      (* Translation of literals of the form a = c.nextat[i] *)
      | F.Literal(F.Atom(E.Eq(E.AddrT a,E.AddrT(E.NextAt(c,i)))))
      | F.Literal(F.Atom(E.Eq(E.AddrT(E.NextAt(c,i)),E.AddrT a)))
      | F.Literal(F.NegAtom(E.InEq(E.AddrT a,E.AddrT(E.NextAt(c,i)))))
      | F.Literal(F.NegAtom(E.InEq(E.AddrT(E.NextAt(c,i)),E.AddrT a))) ->
          let a' = addr_to_tslk_addr a in
          let c' = cell_to_tslk_cell c in
          let i' = int_to_tslk_level i in
          addr_mark_smp_interesting a' true;
          eq_addr a' (NextAt(c',i'))
      (* Translation of literals of the form c' = updCellAddr(c, i, a) *)
      | F.Literal(F.Atom(E.Eq(E.CellT d,E.CellT(E.UpdCellAddr(c,i,a)))))
      | F.Literal(F.Atom(E.Eq(E.CellT(E.UpdCellAddr(c,i,a)),E.CellT d)))
      | F.Literal(F.NegAtom(E.InEq(E.CellT d,E.CellT(E.UpdCellAddr(c,i,a)))))
      | F.Literal(F.NegAtom(E.InEq(E.CellT(E.UpdCellAddr(c,i,a)),E.CellT d))) ->
          begin
            let d' = cell_to_tslk_cell d in
            let c' = cell_to_tslk_cell c in
            let i' = int_to_tslk_level i in
            let a' = addr_to_tslk_addr a in
            let xs = ref [eq_elem (CellData d') (CellData c')] in
            for n = 0 to (k-1) do
              let n' = LevelVal n in
              xs := (F.Implies
                      (eq_level i' n',
                       eq_addr (NextAt(d',n')) a')) ::
                    (F.Implies
                      (ineq_level i' n',
                       eq_addr (NextAt(d',n')) (NextAt(c',n')))) ::
                    (eq_tid (CellLockIdAt(d',n')) (CellLockIdAt(c',n'))) ::
                    (!xs)
            done;
            F.conj_list (!xs)
          end
      | F.Literal l       -> F.Literal (literal_to_tslk_literal l)
      | F.True            -> F.True
      | F.False           -> F.False
      | F.And (f1,f2)     -> F.And (to_formula f1, to_formula f2)
      | F.Or (f1,f2)      -> F.Or (to_formula f1, to_formula f2)
      | F.Not f1          -> F.Not (to_formula f1)
      | F.Implies (f1,f2) -> F.Implies (to_formula f1, to_formula f2)
      | F.Iff (f1,f2)     -> F.Iff (to_formula f1, to_formula f2)



    (**********************  Generic Expression Functions  ********************)

    let cast (phi:Expression.formula) : formula =
      formula_to_tslk_formula phi

    let cast_var (v:Expression.V.t) : V.t =
      var_to_tslk_var v

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

  end

