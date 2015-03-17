
module V : Variable.S
  with type sort = unit
  with type info = unit


type tid =
    VarTh      of V.t
  | NoTid
  | CellLockId of V.t


type expression =
  | Eq            of tid * tid
  | InEq          of tid * tid
  | Pred          of string
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
  | True
  | False
  | And           of expression * expression
  | Or            of expression * expression
  | Not           of expression
  | Implies       of expression * expression
  | Iff           of expression * expression


val all_preds : expression -> string list
val voc : expression -> tid list
val pos : expression -> int list

val keep_locations : Expression.formula -> (expression * string list)
val has_pc : expression -> bool

val expr_to_str : expression -> string

val conj_list : expression list -> expression
val disj_list : expression list -> expression

val expand_pc_range : expression -> expression
val nnf : expression -> expression
val dnf : expression -> expression list list
val cnf : expression -> expression list list

val voc_to_var : tid -> V.t
