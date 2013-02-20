val set_prog_lines : int -> unit
(** [set_prog_lines n] sets the number of program lines to be analyzed to
    [n]. *)

val formula_to_str : Tactics.solve_tactic_t option ->
                     Smp.cutoff_strategy ->
                     Smp.cutoff_options_t ->
                     TllExpression.formula -> string
(** Translates a formula into a string representation for Yices
    following the given strategy. *)

val literal_list_to_str : TllExpression.literal list -> string
(** Translates a list of literals into its corresponding Yices string. *)

val conjformula_to_str : TllExpression.conjunctive_formula -> string
(** Translates a conjunctive formula into a string representation. *)

val get_sort_map : unit -> GenericModel.sort_map_t
(** Gets the declared mapping from elements to sorts *)
