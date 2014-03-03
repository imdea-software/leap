
type sort = Int | Set | Tid

module V : Variable.S
  with type sort = sort
  with type info = unit


type tid =
  | VarTh of V.t
  | NoTid
and integer =
    Val           of int
  | Var           of V.t
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of V.t
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
and term =
  | IntT          of integer
  | SetT          of set
  | FuntermT      of fun_term
  | TidT          of tid
and fun_term =
  | FunVar        of V.t
  | FunUpd        of fun_term * tid * term
and eq =          term * term
and diseq =       term * term
and atom =
    Less          of integer * integer
  | Greater       of integer * integer
  | LessEq        of integer * integer
  | GreaterEq     of integer * integer
  | LessTid       of tid * tid
  | In            of integer * set
  | Subset        of set * set
  | Eq            of eq
  | InEq          of diseq
  | PC            of int * V.shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * V.shared_or_local * bool
and literal = atom Formula.literal

and conjunctive_formula = atom Formula.conjunctive_formula

and formula = atom Formula.formula


exception NotConjunctiveExpr of formula

module ThreadSet : Set.S with type elt = tid

(*
include GenericExpression.S
  with type sort_t := sort
  with type tid_t := tid
  with type t := formula
  with module V := V
  with module ThreadSet := ThreadSet
*)


val build_var : ?fresh:bool ->
                V.id ->
                sort ->
                bool ->
                V.shared_or_local ->
                V.procedure_name ->
                V.t

val is_int_formula : Expression.formula   -> bool

val integer_to_str  : integer  -> string
val formula_to_str  : formula -> string
val literal_to_str  : literal -> string
val funterm_to_str  : fun_term -> string
val atom_to_str     : atom -> string

val all_varid             : formula -> V.id list
val all_global_varid      : formula -> V.id list
val all_local_varid       : formula -> V.id list
val all_varid_set         : formula -> V.VarIdSet.t
val all_global_varid_set  : formula -> V.VarIdSet.t
val all_local_varid_set   : formula -> V.VarIdSet.t

val all_vars              : formula -> V.t list
val all_global_vars       : formula -> V.t list
val all_local_vars        : formula -> V.t list
val all_vars_set          : formula -> V.VarSet.t
val all_global_vars_set   : formula -> V.VarSet.t
val all_local_vars_set    : formula -> V.VarSet.t

val all_global_vars_without_param : formula -> V.t list
val all_local_vars_without_param  : formula -> V.t list

val voc : formula -> tid list


(* LINEARITY *)
val has_variable      : integer -> bool

val formula_is_linear : formula -> bool
val term_is_linear    : integer -> bool


val voc_to_var : tid -> V.t
