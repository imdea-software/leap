
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

type var_info_t

module V : Variable.S
  with type sort = sort
  with type info = var_info_t


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
    VarTh      of V.t
  | NoTid
  | CellLockId of cell
  | BucketTid  of bucket
  | TidArrRd   of tidarr * integer
  | LockId       of lock
and lock =
    VarLock       of V.t
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

(* CALCULATE SET OF VARS *)
module TermSet : Set.S with type elt = term
module AtomSet : Set.S with type elt = atom
module ThreadSet : Set.S with type elt = tid

(* variable manipulation *)
val build_var : ?fresh:bool ->
                ?treat_as_pc:bool ->
                V.id ->
                sort ->
                bool ->
                V.shared_or_local ->
                V.procedure_name ->
                V.t

val treat_as_pc : V.t -> bool


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
val term_to_str     : term    -> string
val addr_to_str     : addr    -> string
val cell_to_str     : cell    -> string
val elem_to_str     : elem    -> string
val tid_to_str      : tid     -> string
val tidarr_to_str   : tidarr  -> string
val mem_to_str      : mem     -> string
val path_to_str     : path    -> string
val set_to_str      : set     -> string
val setth_to_str    : setth   -> string
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

val normalize : formula -> formula
(** [normalize phi] returns a new formula that is the normalization of
    [phi], adding fresh variables if required *)
