
open CommonQuery

module type TSLK_QUERY =
sig

    module Expr : TSLKExpression.S

    include COMMON_QUERY

    val formula_to_str : Tactics.solve_tactic_t option ->
                         Smp.cutoff_strategy ->
                         Smp.cutoff_options_t ->
                         Expr.formula -> string
    (** Translates a formula into a string representation for Yices
        following the given strategy. *)

    val literal_list_to_str : Expr.literal list -> string
    (** Translates a list of literals into its corresponding Yices string. *)

    val conjformula_to_str : Expr.conjunctive_formula -> string
    (** Translates a conjunctive formula into a string representation. *)

end

