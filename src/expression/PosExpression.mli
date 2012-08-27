open Printf
open LeapLib

type variable = string * bool * tid option * string option

and tid =
    VarTh      of variable
  | NoThid
  | CellLockId of variable


type expression =
  | Eq            of tid * tid
  | InEq          of tid * tid
  | Pred          of string
  | PC            of int * tid option * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * tid option * bool
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

val expr_to_str : expression -> string

val conj_list : expression list -> expression
val disj_list : expression list -> expression

val expand_pc_range : expression -> expression
val cnf : expression -> expression list list
