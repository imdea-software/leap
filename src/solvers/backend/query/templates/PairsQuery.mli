open CommonQuery


module type PAIRS_QUERY =
sig

  include COMMON_QUERY

  val set_prog_lines : int -> unit
  (** [set_prog_lines n] sets the number of program lines to [n]. *)

  val pairs_formula_to_str : PairsExpression.formula -> string
  (** Returns the string representation of a formula in the theory of
   *  pairs. *)

  val pairs_formula_with_lines_to_str : PairsExpression.formula -> string
  (** Returns the string representation of a formula in the theory of
   * pairs, taking into consideration the number of lines in the program. *)

  val get_sort_map : unit -> GenericModel.sort_map_t
  (** Gets the declared mapping from elements to sorts *)

end
