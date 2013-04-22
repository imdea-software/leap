
type model_size =
    {
      num_elems : int ;
      num_tids  : int ;
      num_addrs : int ;
    }


val cut_off_normalized  : TllExpression.conjunctive_formula -> model_size

val cut_off             : Smp.cutoff_strategy_t ->
                          Smp.cutoff_options_t ->
                          TllExpression.formula -> model_size

