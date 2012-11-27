
type model_size =
  {
    num_levels : int ;
    num_elems  : int ;
    num_tids   : int ;
    num_addrs  : int ;
  }


module Make (TSLK : TSLKExpression.S) :
  sig

    val cut_off_normalized  : TSLK.conjunctive_formula -> model_size

    val cut_off : Smp.cutoff_strategy ->
                  Smp.cutoff_options_t ->
                  TSLK.formula -> model_size
  end


