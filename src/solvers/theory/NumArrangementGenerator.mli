
(** The type of a numeric arrangement generator *)
type t

(** [new_arr_gen arr] returns a new numeric arrangement generator, using the
 * information contained in [arr] to set the initial restrictions of
 * future generated arrangements. *)
val new_arr_gen : NumExpression.integer Arrangements.t -> t

(** [next_arr ag] generates a new valid numeric arrangement and returns it. If no
 * further valid arrangements exists, then it return the empty lists. *)
val next_arr : t -> NumExpression.integer list list

