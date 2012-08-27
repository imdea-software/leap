type model_size =
    { num_elems : int ; num_tids : int ;
      num_addrs : int ;
    }


type cutoff_strategy = Dnf | Union | Pruning

type cutoff_options_t


val strategy_to_str : cutoff_strategy -> string

val cut_off_normalized  : TllExpression.conjunctive_formula -> model_size

val opt_empty : unit -> cutoff_options_t

val set_forget_primed_mem : cutoff_options_t -> bool -> unit

val set_group_vars : cutoff_options_t -> bool -> unit

val cut_off             : cutoff_strategy ->
                          cutoff_options_t -> TllExpression.formula -> model_size

