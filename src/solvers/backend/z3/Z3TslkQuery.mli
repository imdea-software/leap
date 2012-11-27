module type S =

  sig

    module Expr : TSLKExpression.S

    val prog_lines : int ref
    (** Number of lines in the program *)

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

    val get_sort_map : unit -> GenericModel.sort_map_t
    (** Gets the declared mapping from elements to sorts *)
  end



(*module Make (TSLK : TSLKExpression.S) :*)
module Make (K : Level.S) : S

