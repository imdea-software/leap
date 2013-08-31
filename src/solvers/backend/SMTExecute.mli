
(** All supported SMT solvers *)
type smt_t = Yices | Z3 | CVC4

(** The configuration type for an execution of a SMT solver *)
type configuration_t

(** Exception raised when a query is malformed *)
exception SMT_Syntax_Error of string


(** [new_configuration smt] returns a new configuration containing
    information for executing SMT solver [smt] *)
val new_configuration : smt_t -> configuration_t

(** [reset_calls cfg] restores to zero the calls counter contained in [cfg] *)
val reset_calls : configuration_t -> unit

(** [calls_count cfg] returns the number of calls performed to the SMT solver
    according to [cfg] *)
val calls_count : configuration_t -> int

(** [calls_force_incr cfg] forces manually to increment in one the calls
    counter in [cfg] *)
val calls_force_incr : configuration_t -> unit

(** [compute_model cfg b] enables or disables the generation of a counter
    example model in [cfg] according to [b] *)
val compute_model : configuration_t -> bool -> unit

(** [get_model ()] returns the last generated model containing a counter
    example *)
val get_model : unit -> GenericModel.t

(** [run cfg query] executes the SMT solver whose information is stored in
    [cfg] over the [query], returning [true] if satisfiable and [false] if
    unsatisfiable. Raises [SMT_Syntax_Error] if the query is malformed. *)
val run : configuration_t -> string -> bool
