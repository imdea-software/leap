
exception Unknown_strategy_str of string

type cutoff_strategy_t =
  | Dnf       (* Computes dnf over the formula and then counts literals *)
  | Union     (* Computes an upper bound using union over literals *)
  | Pruning   (* Computes a better bound, by pruning non interesting literals *)


type cutoff_options_t

val def_strategy_list : cutoff_strategy_t list

val strategy_to_str : cutoff_strategy_t -> string

val str_to_strategy : string -> cutoff_strategy_t


val opt_empty : unit -> cutoff_options_t

val set_forget_primed_mem : cutoff_options_t -> bool -> unit

val set_group_vars : cutoff_options_t -> bool -> unit

val forget_primed_mem : cutoff_options_t -> bool

val group_vars : cutoff_options_t -> bool
