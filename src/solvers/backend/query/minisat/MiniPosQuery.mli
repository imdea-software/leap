
val set_prog_lines : int -> unit
(** [set_prog_lines n] sets the number of program lines of the program to
    be analyzed to [n]. *)

val pos_expression_to_str : PosExpression.expression -> string
(** [pos_expression_to_str e] returns the string representation of position
    expression [e] to be passed to Minisat *)
