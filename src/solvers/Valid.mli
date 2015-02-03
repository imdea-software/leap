
exception Unknown_answer_str of string

(** Declares all possibilities answers from the SMT solver for validity *)
type t =
  | Valid
  | Invalid
  | Unknown

val to_str : t -> string
(** [to_str r] returns a string representation of [r] *)

val from_str : string -> t
(** [from_str r] constructs an answer depending on the received string *)

val is_valid : t -> bool
(** [is_valid r] returns true if [r] represents a VALID answer *)

val is_invalid : t -> bool
(** [is_invalid r] returns true if [r] represents a INVALID answer *)

val is_unknown : t -> bool
(** [is_unknown r] returns true if [r] represents a UNKNOWN answer *)
