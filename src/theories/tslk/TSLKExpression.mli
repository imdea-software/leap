
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
    exception Not_tid_var of tid

    (* CALCULATE SET OF VARS *)

    module TermSet : Set.S with type elt = term
    module AtomSet : Set.S with type elt = atom
    module ThreadSet : Set.S with type elt = tid


    include GenericExpression.S
      with type sort_t := sort
      with type tid_t := tid
      with type t := formula
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

module Make (K : Level.S) : S
