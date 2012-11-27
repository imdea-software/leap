

type cutoff_strategy =
  | Dnf       (* Computes dnf over the formula and then counts literals *)
  | Union     (* Computes an upper bound using union over literals *)
  | Pruning   (* Computes a better bound, by pruning non interesting literals *)


type cutoff_options_t


val strategy_to_str : cutoff_strategy -> string


val opt_empty : unit -> cutoff_options_t

val set_forget_primed_mem : cutoff_options_t -> bool -> unit

val set_group_vars : cutoff_options_t -> bool -> unit

val forget_primed_mem : cutoff_options_t -> bool

val group_vars : cutoff_options_t -> bool
