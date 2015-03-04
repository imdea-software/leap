
module Make (TSLK : TSLKExpression.S) :
  sig

    val cut_off_normalized  : TSLK.conjunctive_formula -> ModelSize.t

    val cut_off : Smp.cutoff_strategy_t ->
                  Smp.cutoff_options_t ->
                  TSLK.formula -> ModelSize.t
  end


