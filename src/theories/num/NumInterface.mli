
exception NotAnIntExpression of string


val variable_to_int_variable : Expression.V.t -> NumExpression.V.t
val integer_to_int_integer   : Expression.integer  -> NumExpression.integer
val formula_to_int_formula   : Expression.formula  -> NumExpression.formula

val variable_to_expr_variable : NumExpression.V.t -> Expression.V.t
val integer_to_expr_integer   : NumExpression.integer  -> Expression.integer
val formula_to_expr_formula   : NumExpression.formula  -> Expression.formula
