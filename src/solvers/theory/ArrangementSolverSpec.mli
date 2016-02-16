module type S =
  sig

    val check_sp_dp : int ->
                      int ->
                      Smp.cutoff_strategy_t ->
                      (Expression.integer list list, Sat.t) Hashtbl.t ->
                      Expression.conjunctive_formula ->
                      Expression.integer list list option -> 
                      Sat.t
  end
