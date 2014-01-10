
open CommonQuery

module type TSLK_QUERY =
sig

    module Expr : TSLKExpression.S

    include COMMON_QUERY

    val formula_to_str : Smp.cutoff_strategy_t ->
                         Smp.cutoff_options_t ->
                         bool ->
                         Expr.formula -> string
    (** Translates a formula into a string representation for Yices
        following the given strategy. *)

    val literal_list_to_str : bool -> Expr.literal list -> string
    (** Translates a list of literals into its corresponding Yices string. *)

    val conjformula_to_str : bool -> Expr.conjunctive_formula -> string
    (** Translates a conjunctive formula into a string representation. *)

end

