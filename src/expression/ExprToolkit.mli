module type S =
  sig
    module V : Variable.S

    val defInfo : V.info
    val plain_formula : V.t ExtendedExpression.fol_ops_t ->
                        atom Formula.formula ->
                        atom Formula.formula
  end

