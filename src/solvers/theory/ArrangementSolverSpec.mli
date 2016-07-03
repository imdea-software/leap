module type S =
  sig

    val check_sp_dp : SolverOptions.t ->
                      int ->
                      (Expression.integer list list, Sat.t) Hashtbl.t ->
                      Expression.conjunctive_formula ->
                      Expression.integer list list option -> 
                      Sat.t
  end
