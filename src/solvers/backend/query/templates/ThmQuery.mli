open CommonQuery

module type THM_QUERY =
sig

  include COMMON_QUERY

  val formula_to_str : Smp.cutoff_strategy_t ->
                       Smp.cutoff_options_t ->
                       bool ->
                       ThmExpression.formula -> string
  (** Translates a formula into a string representation for Yices
      following the given strategy. *)

  val literal_list_to_str : bool -> ThmExpression.literal list -> string
  (** Translates a list of literals into its corresponding Yices string. *)

  val conjformula_to_str : bool -> ThmExpression.conjunctive_formula -> string
  (** Translates a conjunctive formula into a string representation. *)

end
