
type sort = Int | Set | Thid

type varId = Expression.varId

type tid = Expression.tid

type shared_or_local = Shared  | Local of tid

type procedure_name  = GlobalScope | Scope of string

type variable =
  {
            id        : varId           ;
            sort      : sort            ;
    mutable is_primed : bool            ;
    mutable parameter : shared_or_local ;
            scope     : procedure_name  ;
  }


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
  | PC            of int * shared_or_local * bool
  | PCUpdate      of int * tid
  | PCRange       of int * int * shared_or_local * bool
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


val build_var : varId ->
                sort ->
                bool ->
                shared_or_local ->
                procedure_name ->
                variable
val var_clear_param_info : variable -> variable
val param_var : variable -> tid -> variable
val var_is_global : variable -> bool


val is_int_formula : Expression.formula   -> bool

val variable_to_str   : variable -> string
val integer_to_str    : integer  -> string
val formula_to_str    : formula -> string
val literal_to_str    : literal -> string

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
