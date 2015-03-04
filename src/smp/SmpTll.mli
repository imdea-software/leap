
val cut_off_normalized  : TllExpression.conjunctive_formula -> ModelSize.t

val cut_off             : Smp.cutoff_strategy_t ->
                          Smp.cutoff_options_t ->
                          TllExpression.formula -> ModelSize.t

