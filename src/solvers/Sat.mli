
exception Unknown_answer_str of string

(** Declares all possibilities answers from the SMT solver for
 * satisfiablity *)
type t =
  | Sat
  | Unsat
  | Unknown


val to_str : t -> string
(** [to_str r] returns a string representation of [r] *)

val from_str : string -> t
(** [from_str r] constructs an answer depending on the received string *)

val is_sat : t -> bool
(** [is_sat r] returns true if [r] represents a SAT answer *)

val is_unsat : t -> bool
(** [is_unsat r] returns true if [r] represents a UNSAT answer *)

val is_unknown : t -> bool
(** [is_unknown r] returns true if [r] represents a UNKNOWN answer *)
