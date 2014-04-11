
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
  | Bool
  | Unknown


module V : Variable.S
  with type sort = sort
  with type info = unit


type term =
    VarT     of V.t
  | SetT     of set
  | ElemT    of elem
  | TidT    of tid
  | AddrT    of addr
  | CellT    of cell
  | SetThT   of setth
  | SetElemT of setelem
  | PathT    of path
  | MemT     of mem
  | IntT     of integer
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
(*  | Malloc of elem * addr * tid *)
and cell =
    VarCell of V.t
  | Error
  | MkCell of elem * addr * tid
  | CellLock of cell * tid
  | CellUnlock of cell
  | CellAt of mem * addr
and setth =
    VarSetTh of V.t
  | EmptySetTh
  | SinglTh   of tid
  | UnionTh   of setth * setth
  | IntrTh    of setth * setth
  | SetdiffTh of setth * setth
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
  | Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
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
  | Getp
  | Set2Elem
  | ElemOrder
  | OrderedList


exception WrongType of term

(* CALCULATE SET OF VARS *)
module TermSet : Set.S with type elt = term
module AtomSet : Set.S with type elt = atom
module ThreadSet : Set.S with type elt = tid

(* variable manipulation *)
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

val get_varset_from_conj         : conjunctive_formula -> V.VarSet.t
val get_varset_from_formula      : formula -> V.VarSet.t
val get_varset_of_sort_from_conj : conjunctive_formula -> sort -> V.VarSet.t
(*val varset_of_sort               : V.VarSet.t -> sort -> V.VarSet.t *)
val get_termset_from_formula     : formula -> TermSet.t
val get_termset_from_conjformula : conjunctive_formula -> TermSet.t
val termset_of_sort              : TermSet.t -> sort -> TermSet.t

val voc_term : term -> ThreadSet.t
val voc : formula -> ThreadSet.t
val voc_conjunctive_formula : conjunctive_formula -> ThreadSet.t
val unprimed_voc : formula -> ThreadSet.t
val voc_to_var : tid -> V.t

(* PRETTY_PRINTERS *)
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
val setelem_to_str  : setelem -> string
val formula_to_str  : formula -> string

(* val eq_to_str      : eq     -> string *)
(* val diseq_to_str   : diseq  -> string *)

val sort_to_str : sort -> string
val variable_list_to_str : V.id list -> string
val typed_variable_list_to_str : (V.id * sort) list -> string

val variable_set_to_str : V.VarIdSet.t -> string
val typed_variable_set_to_str : V.VarSet.t -> string


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
val print_variable_list : V.id list -> unit
val print_typed_variable_list : (V.id * sort) list -> unit
val print_variable_set : V.VarIdSet.t -> unit
val print_typed_variable_set : V.VarSet.t -> unit
  
val generic_printer : ('a -> string) -> 'a -> unit

val required_sorts : formula -> sort list
val special_ops : formula -> special_op_t list

val get_addrs_eqs_conj : conjunctive_formula -> ((addr*addr) list * (addr*addr) list)
val get_addrs_eqs : formula -> ((addr*addr) list * (addr*addr) list)
