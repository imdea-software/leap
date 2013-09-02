
(** Exception raised when a required SAT is not installed in the system *)
exception SAT_Not_Found of string


(** [check_installed ()] checks whether Minisat is installed in the system. *)
val check_installed : unit -> unit
