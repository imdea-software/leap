type pc_t = int

type sort =
  | Set
  | Elem
  | Tid
  | Addr
  | Cell
  | SetTh
  | SetInt
  | SetElem
  | SetPair
  | Path
  | Mem
  | Bool
  | Int
  | Array
  | AddrArray
  | TidArray
  | Unknown


type var_info_t

module V : Variable.S
  with type sort = sort
  with type info = var_info_t

type initVal_t = Equality of term | Condition of formula


and term =
    VarT          of V.t
  | SetT          of set
  | ElemT         of elem
  | TidT          of tid
  | AddrT         of addr
  | CellT         of cell
  | SetThT        of setth
  | SetIntT       of setint
  | SetElemT      of setelem
  | SetPairT      of setpair
  | PathT         of path
  | MemT          of mem
  | IntT          of integer
  | ArrayT        of arrays
  | AddrArrayT    of addrarr
  | TidArrayT     of tidarr

and eq =          term * term

and diseq =       term * term

and arrays =
    VarArray      of V.t
  | ArrayUp       of arrays * tid * expr_t

and addrarr =
  | VarAddrArray  of V.t
  | AddrArrayUp   of addrarr * integer * addr
  | CellArr       of cell

and tidarr =
  | VarTidArray   of V.t
  | TidArrayUp    of tidarr * integer * tid
  | CellTids      of cell

and integer =
    IntVal        of int
  | VarInt        of V.t
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
    VarSet        of V.t
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
    VarTh         of V.t
  | NoTid
  | CellLockId    of cell
  | CellLockIdAt  of cell * integer
  | TidArrayRd   of arrays * tid
  | TidArrRd     of tidarr * integer

and elem =
    VarElem           of V.t
  | CellData          of cell
  | ElemArrayRd       of arrays * tid
  | HavocListElem
  | HavocSkiplistElem
  | LowestElem
  | HighestElem

and addr =
    VarAddr       of V.t
  | Null
  | Next          of cell
  | NextAt        of cell * integer
  | ArrAt         of cell * integer
  | FirstLocked   of mem * path
  | FirstLockedAt of mem * path * integer
  | AddrArrayRd   of arrays * tid
  | AddrArrRd     of addrarr * integer

and cell =
    VarCell       of V.t
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
  | UpdCellAddr   of cell * integer * addr

and setth =
    VarSetTh      of V.t
  | EmptySetTh
  | SinglTh       of tid
  | UnionTh       of setth * setth
  | IntrTh        of setth * setth
  | SetdiffTh     of setth * setth
  | SetThArrayRd  of arrays * tid

and setint =
    VarSetInt     of V.t
  | EmptySetInt
  | SinglInt      of integer
  | UnionInt      of setint * setint
  | IntrInt       of setint * setint
  | SetdiffInt    of setint * setint
  | SetIntArrayRd of arrays * tid

and setelem =
    VarSetElem     of V.t
  | EmptySetElem
  | SinglElem      of elem
  | UnionElem      of setelem * setelem
  | IntrElem       of setelem * setelem
  | SetdiffElem    of setelem * setelem
  | SetToElems     of set * mem
  | SetElemArrayRd of arrays * tid

and setpair =
    VarSetPair     of V.t
  | EmptySetPair
  | SinglPair      of integer * tid
  | UnionPair      of setpair * setpair
  | IntrPair       of setpair * setpair
  | SetdiffPair    of setpair * setpair
  | SetPairArrayRd of arrays * tid

and path =
    VarPath       of V.t
  | Epsilon
  | SimplePath    of addr
  | GetPath       of mem * addr * addr
  | GetPathAt     of mem * addr * addr * integer
  | PathArrayRd   of arrays * tid

and mem =
    VarMem        of V.t
  | Update        of mem * addr * cell
  | MemArrayRd    of arrays * tid

and atom =
    Append        of path * path * path
  | Reach         of mem * addr * addr * path
  | ReachAt       of mem * addr * addr * integer * path
  | OrderList     of mem * addr * addr
  | Skiplist      of mem * set * integer * addr * addr * setelem
  | In            of addr * set
  | SubsetEq      of set * set
  | InTh          of tid * setth
  | SubsetEqTh    of setth * setth
  | InInt         of integer * setint
  | SubsetEqInt   of setint * setint
  | InElem        of elem * setelem
  | SubsetEqElem  of setelem * setelem
  | InPair        of integer * tid * setpair
  | SubsetEqPair  of setpair * setpair
  | Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | LessElem      of elem * elem
  | GreaterElem   of elem * elem
  | Eq            of eq
  | InEq          of diseq
  | BoolVar       of V.t
  | BoolArrayRd   of arrays * tid
  | PC            of pc_t * V.shared_or_local * bool
  | PCUpdate      of pc_t * tid
  | PCRange       of pc_t * pc_t * V.shared_or_local * bool

and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula

(*
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
*)

and expr_t =
    Term          of term
  | Formula       of formula

type tid_subst_t = (tid * tid) list

type var_nature =
  | RealVar
  | GhostVar


type fol_mode_t =
  | PCOnly
  | VarsOnly
  | PCVars


(* TermSet export *)
module TermSet : Set.S with type elt = term
module ThreadSet : Set.S with type elt = tid
module FormulaSet : Set.S with type elt = formula
module PosSet : Set.S with type elt = pc_t




(* Configuration *)
val defCountVar        : integer

(* The heap *)
val heap     : mem


(* VARIABLE FUNCTIONS *)
val build_var : ?fresh:bool ->
                ?nature:var_nature ->
                V.id ->
                sort ->
                bool ->
                V.shared_or_local ->
                V.procedure_name ->
                V.t
val build_global_var : V.id -> sort -> V.t
val build_num_tid_var : int -> V.t
val build_pc_var  : bool -> V.shared_or_local -> V.t

val var_nature : V.t -> var_nature

(** [var_base_info v] returns [v], removing information about priming and
    thread id *)
val var_base_info : V.t -> V.t

val is_pc_var     : V.t -> bool

val var_to_term : V.t -> term
val term_to_var : term -> V.t


(* TERM INFORMATION FUNCTIONS *)
val term_sort : term -> sort


(* Equality constructor functions for formula *)
val eq_set       : set     -> set     -> formula
val eq_elem      : elem    -> elem    -> formula
val eq_tid       : tid     -> tid     -> formula
val eq_addr      : addr    -> addr    -> formula
val eq_cell      : cell    -> cell    -> formula
val eq_setth     : setth   -> setth   -> formula
val eq_setint    : setint  -> setint  -> formula
val eq_setelem   : setelem -> setelem -> formula
val eq_path      : path    -> path    -> formula
val eq_int       : integer -> integer -> formula
val eq_mem       : mem     -> mem     -> formula
val eq_array     : arrays  -> arrays  -> formula
val eq_term      : term    -> term    -> formula
val eq_tid       : tid     -> tid     -> formula
val ineq_addr    : addr    -> addr    -> formula
val ineq_elem    : elem    -> elem    -> formula
val ineq_tid     : tid     -> tid     -> formula
val atom_form    : atom    -> formula
val pc_form      : pc_t -> V.shared_or_local -> bool -> formula
val pcrange_form : pc_t -> pc_t -> V.shared_or_local -> bool -> formula
val pcupd_form   : pc_t -> tid -> formula
val boolvar      : V.t -> formula

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

(* TERM ANALYSIS FUNCTIONS *)
val term_id : term -> V.id
val term_primed : term -> bool
val term_parameter : term -> V.shared_or_local
val term_scope : term -> V.procedure_name
val term_nature : term -> var_nature

(* THREAD LIST GENERATION FUNCTIONS *)
val is_tid_var : tid -> bool
val gen_tid_list : int -> int -> tid list
val gen_tid_list_except : int -> int -> tid -> tid list
val gen_fresh_tid : ThreadSet.t -> tid
val gen_fresh_tid_set : ThreadSet.t -> int -> ThreadSet.t
val gen_fresh_var : V.fresh_var_gen_t-> sort -> V.t


(* LOCALIZATION FUNCTIONS *)
val param_tid_to_str : tid -> string


(* PRIMING FUNCTIONS *)
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
val prime_only   : V.VarSet.t -> bool -> V.VarSet.t -> formula -> formula
val unprime_only : V.VarSet.t -> bool -> V.VarSet.t -> formula -> formula
val prime_term   : term -> term
val unprime_term : term -> term

val primed_vars : formula -> V.t list
val prime_modified : formula -> formula -> formula
val prime_modified_term : formula -> term -> term

val get_vars : formula -> (V.t -> V.VarSet.t) -> V.t list


(* GET VARIABLES FROM EXPRESSION *)
val all_vars : formula -> V.t list
val all_vars_as_set : formula -> V.VarSet.t
val all_local_vars : formula -> V.t list
val all_global_vars : formula -> V.t list


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
val setpair_to_str    : setpair     -> string
val setint_to_str     : setint      -> string
val addrarr_to_str    : addrarr     -> string
val tidarr_to_str     : tidarr      -> string
val eq_to_str         : eq          -> string
val diseq_to_str      : diseq       -> string
val expr_to_str       : expr_t      -> string
val tid_to_str        : tid         -> string
val tid_option_to_str : tid option  -> string
val conjunctive_formula_to_str : conjunctive_formula -> string

val formula_to_human_str : formula -> string


(* CONVERSION FUNCTIONS *)
val array_var_from_term : term -> bool -> arrays
val var_to_term : V.t -> term
val cons_arrayRd_eq_from_var : sort ->
                               tid ->
                               arrays ->
                               initVal_t option ->
                               formula list

val construct_term_eq          : term -> V.shared_or_local -> expr_t ->
                                 (term list * formula)
val construct_term_eq_as_array : term -> V.shared_or_local -> expr_t ->
                                 (term list * formula)

val construct_pres_term        : term -> V.shared_or_local -> formula



(* VOCABULARY FUNCTIONS *)
val voc          : formula -> ThreadSet.t
val unprimed_voc : formula -> ThreadSet.t
val voc_to_var   : tid -> V.t
val voc_to_vars  : ThreadSet.t -> V.VarSet.t

(* GHOST TERMS *)
val var_kind : var_nature -> expr_t -> term list


(* PARAMETRIZATION FUNCTIONS *)
val param_addr : V.shared_or_local -> addr -> addr
val param_elem : V.shared_or_local -> elem -> elem
val param_cell : V.shared_or_local -> cell -> cell
val param_term : V.shared_or_local -> term -> term
val param_expr : V.shared_or_local -> expr_t -> expr_t
val param : V.shared_or_local -> formula -> formula
val param_variable : V.shared_or_local -> V.t -> V.t


(* THREAD SUBSTITUTION FUNCTIONS *)
val new_tid_subst : (tid * tid) list -> tid_subst_t
val new_multiple_tid_subst : tid list -> tid list list -> tid_subst_t list
val new_comb_subst : tid list -> tid list -> tid_subst_t list
val subst_tid : tid_subst_t -> formula -> formula
val subst_to_str : tid_subst_t -> string
val subst_domain : tid_subst_t -> ThreadSet.t
val subst_codomain : tid_subst_t -> ThreadSet.t
val subst_domain_in : ThreadSet.t -> tid_subst_t -> bool
val subst_codomain_in : ThreadSet.t -> tid_subst_t -> bool
val subst_full_domain_assign : tid list -> tid_subst_t -> bool
val subst_full_codomain_assign : tid list -> tid_subst_t -> bool
val is_id_subst : tid_subst_t -> bool


(* VARIABLE SUBSTITUTION FUNCTIONS *)
val subst_vars : V.subst_t -> formula -> formula

(* FORMULA MANIPULATION FUNCTIONS *)
val to_trs : formula -> formula


val to_plain_formula : fol_mode_t -> formula -> formula




(* INITIAL ASSIGNMENT FUNCTION *)
val assign_var : V.t -> initVal_t option -> formula list

val construct_term_set : term list -> TermSet.t
val filter_term_set : term list -> TermSet.t -> TermSet.t


(* NUMERIC EXPRESSION FUNCTIONS *)
val new_num_pos_var_id : string -> int -> V.id
val new_num_pos_var : string -> int -> integer
val new_label_pos_var_id : string -> string -> V.id
val new_label_pos_var : string -> string -> integer

(* Equality constructors *)
val eq_tid    : tid -> tid -> formula
val ineq_tid  : tid -> tid -> formula
val atom_form : atom -> formula

(* Counting abstraction functions *)
val expr_and_removing_true : formula -> formula -> formula
val countAbs_var : int -> V.t
val someone_at : int -> formula
val someone_at_labels : string list -> formula

val build_assign : integer -> integer -> formula
val build_pos_change : int -> int -> formula
val build_label_change : string list -> string list -> formula

(*
val keep_locations : formula -> (formula * (tid * tid) list * (tid * tid) list)
*)


val required_sorts : formula -> sort list
(** [required_sorts phi] returns the list of sorts the formula reasons about *)

val gen_focus_list : pc_t -> pc_t list -> pc_t list -> (bool * pc_t list)
(** [gen_focus_list mp fs is] generates the list of program positions to
    analyze in case that there are at most [mp] positions, [fs] is the list
    of positions where to focus and [is] the positions to ignore. Returns
    a boolean indicating whether the initial position should be considered
    and a list with the positions to be considered (without considering
    position 0 as a member of the list) *)


(* COMPARISON FUNCTIONS. SYNTACTICALLY (almost) IDENTICAL *)
val identical_formula  : formula  -> formula  -> bool
val identical_sorts     : sort     -> sort     -> bool
val identical_variable  : V.t -> V.t -> bool
val identical_term      : term     -> term     -> bool
val identical_eq        : eq -> eq -> bool
val identical_diseq : diseq -> diseq -> bool 
val identical_arrays : arrays -> arrays -> bool
val identical_addrarr : addrarr -> addrarr -> bool
val identical_tidarr : tidarr -> tidarr -> bool
val identical_integer : integer -> integer -> bool
val identical_set : set -> set -> bool
val identical_tid : tid -> tid -> bool
val identical_elem : elem -> elem -> bool
val identical_addr : addr -> addr -> bool
val identical_cell : cell -> cell -> bool
val identical_setth : setth -> setth -> bool
val identical_setint : setint -> setint -> bool
val identical_setelem : setelem -> setelem -> bool
val identical_path : path -> path -> bool
val identical_mem : mem -> mem -> bool
val identical_atom : atom -> atom -> bool
val identical_literal : literal -> literal -> bool
val opposite_literal  : literal -> literal -> bool
val identical_conjunctive_formula : conjunctive_formula -> conjunctive_formula -> bool
val identical_expr_t : expr_t -> expr_t -> bool
