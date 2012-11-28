
val set_prog_lines : int -> unit
(** [set_prog_lines n] sets the number of lines of the program to be analyzed
    to [n]. *)

val pos_expression_to_str : PosExpression.expression -> string
(** Translate a Pos expression into a string. *)

val get_sort_map : unit -> GenericModel.sort_map_t
(** Gets the declared mapping from elements to sorts *)
