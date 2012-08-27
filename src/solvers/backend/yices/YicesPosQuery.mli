val pos_expression_to_str : PosExpression.expression -> int -> string
(** Translate a Pos expression into a string. *)

val get_sort_map : unit -> GenericModel.sort_map_t
(** Gets the declared mapping from elements to sorts *)
