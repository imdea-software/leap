exception NotAnIntExpression of string

type sort = Int | Set | Thid

type varId = Expression.varId

type tid = Expression.tid

type variable = varId * sort * bool * tid option * string option


type integer =
    Val           of int
  | Var           of variable
  | Neg           of integer
  | Add           of integer * integer
  | Sub           of integer * integer
  | Mul           of integer * integer
  | Div           of integer * integer
  | ArrayRd       of Expression.arrays * Expression.tid
  | SetMin        of set
  | SetMax        of set
and set =
    VarSet        of variable
  | EmptySet
  | Singl         of integer
  | Union         of set * set
  | Intr          of set * set
  | Diff          of set * set
and term =
  | IntV          of integer
  | SetV          of set
and fun_term =
  | FunVar        of variable
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
  | TidEq         of tid * tid
  | TidInEq       of tid * tid
  | FunEq         of fun_term * fun_term
  | FunInEq       of fun_term * fun_term
  | PC            of int * tid option * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * tid option * bool
and literal =
    Atom            of atom
  | NegAtom         of atom
and conjunction_literals =
    ConjTrue
  | ConjFalse    
  | Conjuncts     of literal list
and formula =
    Literal       of literal
  | True
  | False
  | And           of formula * formula
  | Or            of formula * formula
  | Not           of formula
  | Implies       of formula * formula
  | Iff           of formula * formula


module VarSet : Set.S with type elt = variable


exception NotConjunctiveExpr of formula


val build_var : varId -> sort -> bool -> tid option -> string option -> variable
val get_id : variable -> varId
val get_sort : variable -> sort
val is_primed_var : variable -> bool
val get_proc : variable -> string option
val get_th : variable -> tid option
val var_clear_param_info : variable -> variable
val param_var : variable -> tid -> variable
val var_is_global : variable -> bool


val is_int_formula : Expression.formula   -> bool

val variable_to_int_variable : Expression.variable -> variable
val integer_to_int_integer   : Expression.integer  -> integer
val term_to_int_integer      : Expression.term     -> integer
val literal_to_int_literal   : Expression.literal  -> literal
val formula_to_int_formula   : Expression.formula  -> formula

val int_variable_to_variable : variable -> Expression.variable
val int_integer_to_integer   : integer  -> Expression.integer
val int_integer_to_term      : integer  -> Expression.term
val int_literal_to_literal   : literal  -> Expression.literal
val int_formula_to_formula   : formula  -> Expression.formula

val variable_to_string       : variable -> string
val int_integer_to_string    : integer  -> string
val int_formula_to_string    : formula -> string
val int_literal_to_string    : literal -> string

val all_varid             : formula -> Expression.varId list
val all_varid_literal     : literal -> Expression.varId list
val all_global_varid      : formula -> Expression.varId list
val all_local_varid       : formula -> Expression.varId list
val all_varid_set         : formula -> Expression.VarIdSet.t
val all_varid_set_literal : literal -> Expression.VarIdSet.t
val all_global_varid_set  : formula -> Expression.VarIdSet.t
val all_local_varid_set   : formula -> Expression.VarIdSet.t

val all_vars              : formula -> variable list
val all_vars_literal      : literal -> variable list
val all_global_vars       : formula -> variable list
val all_local_vars        : formula -> variable list
val all_vars_set          : formula -> VarSet.t
val all_vars_set_literal  : literal -> VarSet.t
val all_global_vars_set   : formula -> VarSet.t
val all_local_vars_set    : formula -> VarSet.t

val all_global_vars_without_param : formula -> variable list
val all_local_vars_without_param  : formula -> variable list

val voc : formula -> tid list

(* CONJUNCTIONS OF LITERALS *)
val is_conjunctive            : formula -> bool
val formula_to_conj_literals  : formula -> literal list
val list_literals_to_formula  : literal list -> formula
val conj_literals_to_formula  : conjunction_literals -> formula


(* LINEARITY *)
val has_variable      : integer -> bool

val formula_is_linear : formula -> bool
val term_is_linear    : integer -> bool
val literal_is_linear : literal -> bool

