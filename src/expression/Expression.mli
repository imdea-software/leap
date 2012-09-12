
type varId = string

type kind_t = Normal | Ghost

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

and tidarr =
  | VarTidArray   of variable
  | TidArrayUp    of tidarr * integer * tid

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

and set =
    VarSet        of variable
  | EmptySet
  | Singl         of addr
  | Union         of set * set
  | Intr          of set * set
  | Setdiff       of set * set
  | PathToSet     of path
  | AddrToSet     of mem * addr
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
  | AddrArrayRd   of arrays * tid
  | AddrArrRd     of addrarr * integer

and cell =
    VarCell       of variable
  | Error
  | MkCell        of elem * addr * tid
  | MkSLCell      of elem * addrarr * tidarr * integer
  | CellLock      of cell
  | CellLockAt    of cell * integer
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
  | PathArrayRd   of arrays * tid

and mem =
    VarMem        of variable
  | Update        of mem * addr * cell
  | MemArrayRd    of arrays * tid

and atom =
    Append        of path * path * path
  | Reach         of mem * addr * addr * path
  | OrderList     of mem * addr * addr
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
    formula : formula;
    primed : formula;
    voc : tid list;
    vars : variable list;
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

module Pool (PType:PoolType) : P with type elt = PType.t

(* Pool type for tagging expression, formulas, etc. *)

(* TermPool export *)
module TermPool : P with type elt = term


(* TermSet export *)
module TermSet : Set.S with type elt = term
module VarIdSet : Set.S with type elt = varId
module VarSet : Set.S with type elt = variable
module ThreadSet : Set.S with type elt = tid
module PosSet : Set.S with type elt = pc_t




(* Configuration *)
val pc_name         : string
val fresh_cell_name : string
val fresh_addr_name : string
val defCountAbsVar  : string
val defCountVar     : integer

(* The heap *)
val heap     : mem
val aux_heap : mem


(* Fresh auxiliary variables *)
val fresh_cell : cell


(* PROGRAM POSITION FUNCTIONS *)
val build_pc_range : pc_t -> pc_t -> pc_t list


(* VARIABLE FUNCTIONS *)
val same_var : variable -> variable -> bool
val build_var : varId -> sort -> bool -> tid option ->
                string option -> kind_t -> variable
val var_clear_param_info : variable -> variable

val var_id        : variable -> varId
val var_sort      : variable -> sort
val var_pr        : variable -> bool
val var_th        : variable -> tid option
val var_proc      : variable -> string option
val var_k         : variable -> kind_t
val var_val       : variable -> int
val var_full_info : variable -> (varId * sort * bool *
                                 tid option * string option * kind_t)

val is_local_var  : variable -> bool
val is_global_var : variable -> bool
val var_sort      : variable -> sort

val build_num_tid : int -> tid
val build_var_tid : varId -> tid

val inject_var_sort : variable -> sort -> variable

val var_to_term : variable -> term
val term_to_var : term -> variable


(* TERM INFORMATION FUNCTIONS *)
val term_sort : term -> sort


(* Equality constructor functions for formula *)
val eq_set     : set     -> set     -> formula
val eq_elem    : elem    -> elem    -> formula
val eq_tid     : tid     -> tid     -> formula
val eq_addr    : addr    -> addr    -> formula
val eq_cell    : cell    -> cell    -> formula
val eq_setth   : setth   -> setth   -> formula
val eq_setint  : setint  -> setint  -> formula
val eq_setelem : setelem -> setelem -> formula
val eq_path    : path    -> path    -> formula
val eq_int     : integer -> integer -> formula
val eq_mem     : mem     -> mem     -> formula
val eq_array   : arrays  -> arrays  -> formula
val eq_term    : term    -> term    -> formula
val eq_tid     : tid     -> tid     -> formula
val ineq_addr  : addr    -> addr    -> formula
val ineq_elem  : elem    -> elem    -> formula
val ineq_tid   : tid     -> tid     -> formula
val atom_form  : atom    -> formula
val pc_form    : pc_t -> tid option -> bool -> formula
val pcupd_form : pc_t -> tid -> formula
val boolvar    : variable -> formula

val less_form      : integer -> integer -> formula
val lesseq_form    : integer -> integer -> formula
val greater_form   : integer -> integer -> formula
val greatereq_form : integer -> integer -> formula
val subset_form    : set     -> set     -> formula
val subsetth_form  : setth   -> setth   -> formula
val subsetint_form : setint  -> setint  -> formula
val in_form        : addr    -> set     -> formula
val inth_form      : tid     -> setth   -> formula
val inint_form     : integer -> setint  -> formula




(* THREAD IDENTIFIER INFORMATION FUNCTIONS *)
val is_tid_var : tid -> bool
val is_tid_val : tid -> bool
val is_tid_lockid : tid -> bool


(* VARIABLE INFORMATION FUNCTIONS *)
val var_info_sort : var_info_t -> sort
val var_info_expr : var_info_t -> initVal_t option
val var_info_tid  : var_info_t -> tid option
val var_info_kind : var_info_t -> kind_t
val get_var_id     : term -> varId
val get_var_thread : term -> tid option
val get_var_owner  : term -> string option
val get_var_kind   : term -> kind_t


(* THREAD LIST GENERATION FUNCTIONS *)
val is_tid_var : tid -> bool
val gen_thread_list : int -> int -> tid list
val gen_thread_list_except : int -> int -> tid -> tid list
val gen_fresh_thread : tid list -> tid
val gen_fresh_thread_list : tid list -> int -> tid list


(* LOCALIZATION FUNCTIONS *)
val localize_var_id : varId -> string -> varId
val loc_var_option :varId -> string option -> varId


(* PRIMING FUNCTIONS *)
val is_primed    : variable -> bool
(*val prime_var_name : varId -> varId*)
val prime_addr   : addr -> addr
val prime_elem   : elem -> elem
val prime_cell   : cell -> cell
val prime_mem    : mem  -> mem
val prime_int    : integer -> integer

val prime_tid    : tid -> tid
val unprime_tid  : tid -> tid

val prime_term   : term -> term
val unprime_term : term -> term
val prime        : formula -> formula
val unprime      : formula -> formula
val prime_only   : VarSet.t -> formula -> formula
val unprime_only : VarSet.t -> formula -> formula
val prime_term   : term -> term
val unprime_term : term -> term

val primed_vars : formula -> variable list
val prime_modified : formula -> formula -> formula
val prime_modified_term : formula -> term -> term

val get_vars : formula -> (variable -> VarSet.elt list) -> variable list


(* GET VARIABLES FROM EXPRESSION *)
val all_vars : formula -> variable list
val all_vars_as_set : formula -> VarSet.t
val all_local_vars : formula -> variable list
val all_local_owned_vars : formula -> variable list
val all_global_vars : formula -> variable list


(* EXPRESSION CONVERSION FUNCTIONS *)
val get_initVal_restriction : initVal_t -> expr_t
val term_to_integer : term -> integer
val term_to_set : term -> set
val term_to_setth : term -> setth
val term_to_setint : term -> setint


(* PRINTING FUNCTIONS *)
val pc_to_str         : pc_t        -> string
val sort_to_str       : sort        -> string
val formula_to_str    : formula     -> string
val literal_to_str    : literal     -> string
val atom_to_str       : atom        -> string
val term_to_str       : term        -> string
val addr_to_str       : addr        -> string
val cell_to_str       : cell        -> string
val elem_to_str       : elem        -> string
val tid_to_str        : tid         -> string
val arrays_to_str     : arrays      -> string
val integer_to_str    : integer     -> string
val mem_to_str        : mem         -> string
val path_to_str       : path        -> string
val set_to_str        : set         -> string
val setth_to_str      : setth       -> string
val setelem_to_str    : setelem     -> string
val setint_to_str     : setint      -> string
val eq_to_str         : eq          -> string
val diseq_to_str      : diseq       -> string
val expr_to_str       : expr_t      -> string
val tid_to_str        : tid        -> string
val tid_option_to_str : tid option -> string

val variable_to_str  : variable    -> string


(* CONVERSION FUNCTIONS *)
val array_var_from_term : term -> bool -> arrays
val construct_var_from_sort : varId -> tid option -> string option -> sort -> 
                                kind_t -> term
val convert_var_to_term : string option -> varId -> var_info_t -> term
val cons_arrayRd_eq_from_var : sort ->
                               tid ->
                               arrays ->
                               initVal_t option ->
                               formula list

val construct_term_eq          : term -> tid option -> expr_t ->
                                 (term list * formula)
val construct_term_eq_as_array : term -> tid option -> expr_t ->
                                 (term list * formula)

val construct_pres_term        : term -> tid option -> formula



(* VOCABULARY FUNCTIONS *)
val voc          : formula -> tid list
val unprimed_voc : formula -> tid list


(* GHOST TERMS *)
val var_kind : kind_t -> expr_t -> term list


(* PARAMETRIZATION FUNCTIONS *)
val param_addr : tid option -> addr -> addr
val param_cell : tid option -> cell -> cell
val param_term : tid option -> term -> term
val param_expr : tid option -> expr_t -> expr_t
val param : tid option -> formula -> formula
val param_variable : tid option -> variable -> variable


(* THREAD SUBSTITUTION FUNCTIONS *)
val new_tid_subst : (tid * tid) list -> tid_subst_t
val new_multiple_tid_subst : tid list -> tid list list -> tid_subst_t list
val new_comb_subst : tid list -> tid list -> tid_subst_t list
val subst_tid : tid_subst_t -> formula -> formula
val subst_to_str : tid_subst_t -> string
val subst_domain : tid_subst_t -> ThreadSet.t
val subst_codomain : tid_subst_t -> ThreadSet.t
val subst_domain_in : tid list -> tid_subst_t -> bool
val subst_codomain_in : tid list -> tid_subst_t -> bool
val subst_full_assign : tid list -> tid_subst_t -> bool

(* FORMULA MANIPULATION FUNCTIONS *)
val conj_list : formula list -> formula
val disj_list : formula list -> formula
val to_conj_list : formula -> formula list
val dnf : formula -> formula list list
val cnf : formula -> formula list list
val dnf_count : formula -> (float * float)
val to_trs : formula -> formula
val conj_literals : literal list -> formula
val disj_literals : literal list -> formula




(* INITIAL ASSIGNMENT FUNCTION *)
val assign_var : string option -> varId -> var_info_t -> formula list



(* TERMSET MANIPULATION FUNCTIONS *)
val construct_term_set : term list -> TermSet.t
val filter_term_set : term list -> TermSet.t -> TermSet.t


(* VARSET MANIPULATION FUNCTIONS *)
val construct_varid_set : varId list -> VarIdSet.t
val construct_var_set : variable list -> VarSet.t


(* NUMERIC EXPRESSION FUNCTIONS *)
val new_num_pos_var_id : string -> int -> varId
val new_num_pos_var : string -> int -> integer
val new_label_pos_var_id : string -> string -> varId
val new_label_pos_var : string -> string -> integer
val check_numeric : varId -> var_info_t -> unit

(* Equality constructors *)
val eq_tid    : tid -> tid -> formula
val ineq_tid  : tid -> tid -> formula
val atom_form : atom -> formula

(* Counting abstraction functions *)
val expr_and_removing_true : formula -> formula -> formula
val countAbs_var : int -> variable
val someone_at : int -> formula
val someone_at_labels : string list -> formula

val build_assign : integer -> integer -> formula
val build_pos_change : int -> int -> formula
val build_label_change : string list -> string list -> formula

(*
val keep_locations : formula -> (formula * (tid * tid) list * (tid * tid) list)
*)

val new_formula_info : formula -> formula_info_t



val cleanup : formula -> formula
(** [cleanup phi] removes redundant information from [phi], like
    [True] in conjunctions *)

val cleanup_dup : formula list -> formula list
(** [cleanup_dup ps] assumes that the given list express a conjunction of
    formulas and removes all duplicated formulas from the list *)

val required_sorts : formula -> sort list
(** [required_sorts phi] returns the list of sorts the formula reasons about *)

val gen_focus_list : pc_t -> pc_t list -> pc_t list -> pc_t list
(** [gen_focus_list mp fs is] generates the list of program positions to
    analyze in case that there are at most [mp] positions, [fs] is the list
    of positions where to focus and [is] the positions to ignore *)
