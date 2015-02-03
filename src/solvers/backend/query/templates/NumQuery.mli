open CommonQuery


module type NUM_QUERY =
sig

  include COMMON_QUERY

  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of program lines to [n]. *)

  val int_varlist_to_str : NumExpression.V.t list -> string
  (** Translates a list of integer variables into its string representation *)

  val string_of_formula  : NumExpression.formula -> string
  (** Translates a numeric formula into a Yices string *)

  val string_of_literal  : NumExpression.literal -> string
  (** Translates a literal into its corresponding Yices string representation. *)

  val int_formula_to_str : NumExpression.formula -> string
  (** Returns the string representation of an integer formula. *)

  val int_formula_with_lines_to_str : NumExpression.formula -> string
  (** Returns the string representation of an integer formula, taking into account
      the number of lines in the program. *)

  val standard_widening : NumExpression.V.t list ->
                          NumExpression.formula ->
                          NumExpression.literal ->
                          string
  (** Returns the string representation of a standard widening. *)

  val get_sort_map : unit -> GenericModel.sort_map_t
  (** Gets the declared mapping from elements to sorts *)

end
