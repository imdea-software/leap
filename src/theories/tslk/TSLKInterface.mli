

module Make (TSLK : TSLKExpression.S) :
  sig
    val formula_to_tslk_formula : Expression.formula -> TSLK.formula

    val sort_to_tslk_sort : Expression.sort -> TSLK.sort

    val sort_to_expr_sort : TSLK.sort -> Expression.sort

  end

