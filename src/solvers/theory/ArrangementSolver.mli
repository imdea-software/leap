module type S =
  sig

    val try_sat_with_pa : Expression.formula -> Sat.t

    val dnf_sat : SolverOptions.t ->
                  Expression.conjunctive_formula ->
                  Sat.t
    
  end

module Make (AS : ArrangementSolverSpec.S) : S
