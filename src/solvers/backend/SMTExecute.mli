
type smt_t = Yices | Z3 | CVC4

type configuration_t


val new_configuration : smt_t -> configuration_t


val reset_calls : configuration_t -> unit
val calls_count : configuration_t -> int
val compute_model : configuration_t -> bool -> unit
val get_model : unit -> GenericModel.t

val run : configuration_t -> string -> bool
