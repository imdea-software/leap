
module type S =
  sig

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
    val get_varset_from_formula      : formula -> VarSet.t
    val get_varset_of_sort_from_conj : conjunctive_formula -> sort -> VarSet.t
    val varset_of_sort               : VarSet.t -> sort -> VarSet.t
    val get_termset_from_formula     : formula -> TermSet.t
    val get_termset_from_conjformula : conjunctive_formula -> TermSet.t
    val termset_of_sort              : TermSet.t -> sort -> TermSet.t

    val voc_term : term -> tid list
    val voc : formula -> tid list
    val conjformula_voc : conjunctive_formula -> tid list
    val unprimed_voc : formula -> tid list

    val nnf : formula -> formula
    val dnf : formula -> conjunctive_formula list

    val prime_var : variable -> variable
    val unprime_var : variable -> variable
    val is_primed_var : variable -> bool


    (* PRETTY_PRINTERS *)
    val variable_to_str : variable -> string
    val atom_to_str     : atom    -> string
    val literal_to_str  : literal -> string
    val conjunctive_formula_to_str : conjunctive_formula -> string
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

  end

module Make (K : Level.S) : S
