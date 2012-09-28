

type cutoff_strategy =
  | Dnf       (* Computes dnf over the formula and then counts literals *)
  | Union     (* Computes an upper bound using union over literals *)
  | Pruning   (* Computes a better bound, by pruning non interesting literals *)


type cutoff_options_t


type model_size =
  {
    num_levels : int ;
    num_elems  : int ;
    num_tids   : int ;
    num_addrs  : int ;
  }

  val strategy_to_str : cutoff_strategy -> string

  val opt_empty : unit -> cutoff_options_t

  val set_forget_primed_mem : cutoff_options_t -> bool -> unit

  val set_group_vars : cutoff_options_t -> bool -> unit


module Make (TSLK : TSLKExpression.S) :
  sig

    val cut_off_normalized  : TSLK.conjunctive_formula -> model_size

    val cut_off : cutoff_strategy ->
                  cutoff_options_t -> TSLK.formula -> model_size
  end


