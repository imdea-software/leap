

module Make (TSLK : TSLKExpression.S) :
  sig
    val formula_to_tslk_formula : Expression.formula -> TSLK.formula
  end

