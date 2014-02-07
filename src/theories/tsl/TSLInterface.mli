

val var_to_tsl_var : Expression.V.t -> TSLExpression.V.t
val tid_to_tsl_tid : Expression.tid -> TSLExpression.tid
val term_to_tsl_term : Expression.term -> TSLExpression.term
val set_to_tsl_set : Expression.set -> TSLExpression.set
val elem_to_tsl_elem : Expression.elem -> TSLExpression.elem
val addr_to_tsl_addr : Expression.addr -> TSLExpression.addr
val cell_to_tsl_cell : Expression.cell -> TSLExpression.cell
val setth_to_tsl_setth : Expression.setth -> TSLExpression.setth
val setelem_to_tsl_setelem : Expression.setelem -> TSLExpression.setelem
val path_to_tsl_path : Expression.path -> TSLExpression.path
val mem_to_tsl_mem : Expression.mem -> TSLExpression.mem
val int_to_tsl_int : Expression.integer -> TSLExpression.integer
val addrarr_to_tsl_addrarr : Expression.addrarr -> TSLExpression.addrarr
val tidarr_to_tsl_tidarr : Expression.tidarr -> TSLExpression.tidarr
val formula_to_tsl_formula : Expression.formula -> TSLExpression.formula


val var_to_expr_var : TSLExpression.V.t -> Expression.V.t
val tid_to_expr_tid : TSLExpression.tid -> Expression.tid
val term_to_expr_term : TSLExpression.term -> Expression.term
val set_to_expr_set : TSLExpression.set -> Expression.set
val elem_to_expr_elem : TSLExpression.elem -> Expression.elem
val addr_to_expr_addr : TSLExpression.addr -> Expression.addr
val cell_to_expr_cell : TSLExpression.cell -> Expression.cell
val setth_to_expr_setth : TSLExpression.setth -> Expression.setth
val setelem_to_expr_setelem : TSLExpression.setelem -> Expression.setelem
val path_to_expr_path : TSLExpression.path -> Expression.path
val mem_to_expr_mem : TSLExpression.mem -> Expression.mem
val int_to_expr_int : TSLExpression.integer -> Expression.integer
val addrarr_to_expr_addrarr : TSLExpression.addrarr -> Expression.addrarr
val tidarr_to_expr_tidarr : TSLExpression.tidarr -> Expression.tidarr
val formula_to_expr_formula : TSLExpression.formula -> Expression.formula
