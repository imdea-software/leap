
exception NotAPairsExpression of string


val variable_to_pairs_variable : Expression.V.t -> PairsExpression.V.t
val integer_to_pairs_integer   : Expression.integer  -> PairsExpression.integer
val formula_to_pairs_formula   : Expression.formula  -> PairsExpression.formula

val variable_to_expr_variable : PairsExpression.V.t -> Expression.V.t
val integer_to_expr_integer   : PairsExpression.integer  -> Expression.integer
val formula_to_expr_formula   : PairsExpression.formula  -> Expression.formula
