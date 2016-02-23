

val sort_to_thm_sort : Expression.sort -> ThmExpression.sort
val var_to_thm_var : Expression.V.t -> ThmExpression.V.t
val tid_to_thm_tid : Expression.tid -> ThmExpression.tid
val term_to_thm_term : Expression.term -> ThmExpression.term
val set_to_thm_set : Expression.set -> ThmExpression.set
val elem_to_thm_elem : Expression.elem -> ThmExpression.elem
val addr_to_thm_addr : Expression.addr -> ThmExpression.addr
val cell_to_thm_cell : Expression.cell -> ThmExpression.cell
val setth_to_thm_setth : Expression.setth -> ThmExpression.setth
val setelem_to_thm_setelem : Expression.setelem -> ThmExpression.setelem
val path_to_thm_path : Expression.path -> ThmExpression.path
val mem_to_thm_mem : Expression.mem -> ThmExpression.mem
val int_to_thm_int : Expression.integer -> ThmExpression.integer
val literal_to_thm_literal : Expression.literal -> ThmExpression.literal
val conj_formula_to_thm_conj_formula : Expression.conjunctive_formula ->
                                       ThmExpression.conjunctive_formula
val formula_to_thm_formula : Expression.formula -> ThmExpression.formula


val sort_to_expr_sort : ThmExpression.sort -> Expression.sort
val var_to_expr_var : ThmExpression.V.t -> Expression.V.t
val tid_to_expr_tid : ThmExpression.tid -> Expression.tid
val term_to_expr_term : ThmExpression.term -> Expression.term
val set_to_expr_set : ThmExpression.set -> Expression.set
val elem_to_expr_elem : ThmExpression.elem -> Expression.elem
val addr_to_expr_addr : ThmExpression.addr -> Expression.addr
val cell_to_expr_cell : ThmExpression.cell -> Expression.cell
val setth_to_expr_setth : ThmExpression.setth -> Expression.setth
val setelem_to_expr_setelem : ThmExpression.setelem -> Expression.setelem
val path_to_expr_path : ThmExpression.path -> Expression.path
val mem_to_expr_mem : ThmExpression.mem -> Expression.mem
val int_to_expr_int : ThmExpression.integer -> Expression.integer
val literal_to_expr_literal : ThmExpression.literal -> Expression.literal
val conj_formula_to_expr_conj_formula : ThmExpression.conjunctive_formula ->
                                        Expression.conjunctive_formula
val formula_to_expr_formula : ThmExpression.formula -> Expression.formula

