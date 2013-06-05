
exception NotAnIntExpression of string


val variable_to_int_variable : Expression.variable -> NumExpression.variable
val integer_to_int_integer   : Expression.integer  -> NumExpression.integer
val literal_to_int_literal   : Expression.literal  -> NumExpression.literal
val formula_to_int_formula   : Expression.formula  -> NumExpression.formula

val variable_to_expr_variable : NumExpression.variable -> Expression.variable
val integer_to_expr_integer   : NumExpression.integer  -> Expression.integer
val literal_to_expr_literal   : NumExpression.literal  -> Expression.literal
val formula_to_expr_formula   : NumExpression.formula  -> Expression.formula
