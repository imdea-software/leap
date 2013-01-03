

module Make (TSLK : TSLKExpression.S) :
  sig
    val sort_to_tslk_sort : Expression.sort -> TSLK.sort

    val literal_to_tslk_literal : Expression.literal -> TSLK.literal

    val formula_to_tslk_formula : Expression.formula -> TSLK.formula

    val sort_to_expr_sort : TSLK.sort -> Expression.sort

    val literal_to_expr_literal : TSLK.literal -> Expression.literal

    val formula_to_expr_formula : TSLK.formula -> Expression.formula

  end

