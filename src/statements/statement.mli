
type st_info_t = {
  (** Current statement position *)
  pos                     : Expression.pc_t;
  (** Next statement position *)
  mutable next_pos        : Expression.pc_t;
  (** Position where to jump if statement was a conditional and
      the condition is not satisfied *)
  mutable else_pos        : Expression.pc_t;
  (** Position where the invoked procedure begins in case of a call statement *)
  mutable call_pos        : Expression.pc_t option;
  (** Optional next positions in case of a non-deterministic choice *)
  mutable opt_pos         : Expression.pc_t list;
  (** Positions from where a procedure has been invoked *)
  mutable called_from_pos : Expression.pc_t list;
  (** Positions where to return after a return in a procedure *)
  mutable return_pos      : Expression.pc_t list;
  }


type varId = Expression.varId

type kind_t = Normal | Ghost

type unit_op = Lock | Unlock


(* Expression representation in program statements *)

type variable =
  {
            id        : varId                     ;
            sort      : Expression.sort           ;
            scope     : Expression.procedure_name ;
            nature    : Expression.var_nature     ;
  }


type term =
    VarT          of variable
  | SetT          of set
  | ElemT         of elem
  | TidT         of tid
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
  | VarTh           of variable
  | NoTid
  | CellLockId      of cell
  | CellLockIdAt    of cell * integer
  | TidArrayRd     of arrays * tid
  | PointerLockid   of addr
  | PointerLockidAt of addr * integer
  | TidArrRd       of tidarr * integer

and elem =
    VarElem           of variable
  | CellData          of cell
  | ElemArrayRd       of arrays * tid
  | PointerData       of addr
  | HavocListElem
  | HavocSkiplistElem
  | LowestElem
  | HighestElem

and addr =
  | VarAddr       of variable
  | Null
  | Next          of cell
  | NextAt        of cell * integer
  | ArrAt         of cell * integer
  | FirstLocked   of mem * path
  | AddrArrayRd   of arrays * tid
  | Malloc        of elem * addr * tid
  | MallocSL      of elem * integer
  | MallocSLK     of elem * integer
  | PointerNext   of addr
  | PointerNextAt of addr * integer
  | PointerArrAt  of addr * integer
  | AddrArrRd     of addrarr * integer

and cell =
    VarCell       of variable
  | Error
  | MkCell        of elem * addr * tid
  | MkSLKCell     of elem * addr list * tid list
  | MkSLCell      of elem * addrarr * tidarr * integer
  | CellLock      of cell
  | CellUnlock    of cell
  | CellLockAt    of cell * integer
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

and literal =
    Append        of path * path * path
  | Reach         of mem * addr * addr * path
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

and boolean =
    Literal       of literal
  | True
  | False
  | And           of boolean * boolean
  | Or            of boolean * boolean
  | Not           of boolean
  | Implies       of boolean * boolean
  | Iff           of boolean * boolean


and expr_t =
    Term          of term
  | Formula       of boolean


type unit_operation =
    UnitLock      of addr
  | UnitUnlock    of addr
  | UnitLockAt    of addr * integer
  | UnitUnlockAt  of addr * integer


type statement_t =
    StSkip of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAssert of
      boolean            *  (* Condition *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAwait of
      boolean            *  (* Condition *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StNonCrit of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StCrit of
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StIf of
      boolean            *  (* Condition *)
      statement_t        *  (* True branch *)
      statement_t option *  (* False branch *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StWhile of
      boolean            *  (* Condition *)
      statement_t        *  (* Loop *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StSelect of
      statement_t list   *  (* Options *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAssign of
      term               *  (* Variable *)
      expr_t             *  (* Expression *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StUnit of
      unit_operation     *  (* Unit operation *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StAtomic of
      statement_t list   *  (* Atomic statements *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StSeq of
      statement_t list      (* Statement list *)
  | StCall of
      term option        *  (* Possible assignment term *)
      string             *  (* Procedure name *)
      term list          *  (* Call arguments *)
      statement_t option *  (* Ghost code *)
      st_info_t option
  | StReturn of
      term option        *  (* Return value *)
      statement_t option *  (* Ghost code *)
      st_info_t option


(* General constants *)
val me_tid : tid


(* Variable functions *)
val build_var : varId ->
                Expression.sort ->
                Expression.procedure_name ->
                Expression.var_nature ->
                variable
val var_replace_sort : variable -> Expression.sort -> variable


(* Auxiliary functions *)
val construct_var_from_sort : Expression.varId ->
                              Expression.procedure_name ->
                              Expression.sort ->
                              Expression.var_nature ->
                              term

(* Pretty printing functions *)
val term_to_str    : term -> string
val boolean_to_str : boolean -> string
val expr_to_str    : expr_t -> string


(* Ghost variables query functions *)
val var_kind : Expression.var_nature -> expr_t -> term list


(* Statement conversion functions *)
val term_to_integer : term -> integer
val term_to_set     : term -> set
val term_to_setth   : term -> setth
val term_to_setint  : term -> setint
val term_to_setelem : term -> setelem

val elem_to_expr_elem : elem -> Expression.elem
val addr_to_expr_addr : addr -> Expression.addr
val tid_to_expr_tid : tid -> Expression.tid
val integer_to_expr_integer : integer -> Expression.integer

val term_to_expr_term : term -> Expression.term
val literal_to_expr_literal : literal -> Expression.literal
val boolean_to_expr_formula : boolean -> Expression.formula
val expr_to_expr_expr : expr_t -> Expression.expr_t


(* Statement query functions *)
val get_st_info : statement_t -> st_info_t
val get_st_pos : statement_t -> Expression.pc_t
val get_st_else_pos : statement_t -> Expression.pc_t
val get_st_next_pos : statement_t -> Expression.pc_t
val get_st_call_pos : statement_t -> Expression.pc_t option
val get_forced_st_pos : statement_t -> Expression.pc_t
val get_forced_st_else_pos : statement_t -> Expression.pc_t
val get_forced_st_next_pos : statement_t -> Expression.pc_t
val get_last_st_info : statement_t -> st_info_t
val get_last_st_pos : statement_t -> Expression.pc_t
val get_fst_st_pos : statement_t -> Expression.pc_t

val statement_to_str : int -> statement_t -> string

val addr_used_in_unit_op : unit_operation -> Expression.addr
val level_used_in_unit_op : unit_operation -> Expression.integer
val get_unit_op : unit_operation -> unit_op

val enabling_condition : Expression.shared_or_local ->
                         statement_t ->
                         Expression.formula list
