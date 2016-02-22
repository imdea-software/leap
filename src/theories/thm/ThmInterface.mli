
val literal_to_thm_literal : Expression.literal -> ThmExpression.literal
val conj_formula_to_thm_conj_formula : Expression.conjunctive_formula ->
                                       ThmExpression.conjunctive_formula
val formula_to_thm_formula : Expression.formula -> ThmExpression.formula


val literal_to_expr_literal : ThmExpression.literal -> Expression.literal
val conj_formula_to_expr_conj_formula : ThmExpression.conjunctive_formula ->
                                        Expression.conjunctive_formula
val formula_to_expr_formula : ThmExpression.formula -> Expression.formula

val sort_to_thm_sort : Expression.sort -> ThmExpression.sort
val sort_to_expr_sort : ThmExpression.sort -> Expression.sort
