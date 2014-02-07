

module Make (TSLK : TSLKExpression.S) :
  sig
    val sort_to_tslk_sort : Expression.sort -> TSLK.sort
    val var_to_tslk_var : Expression.V.t -> TSLK.V.t
    val tid_to_tslk_tid : Expression.tid -> TSLK.tid
    val term_to_tslk_term : Expression.term -> TSLK.term
    val set_to_tslk_set : Expression.set -> TSLK.set
    val elem_to_tslk_elem : Expression.elem -> TSLK.elem
    val addr_to_tslk_addr : Expression.addr -> TSLK.addr
    val cell_to_tslk_cell : Expression.cell -> TSLK.cell
    val setth_to_tslk_setth : Expression.setth -> TSLK.setth
    val setelem_to_tslk_setelem : Expression.setelem -> TSLK.setelem
    val path_to_tslk_path : Expression.path -> TSLK.path
    val mem_to_tslk_mem : Expression.mem -> TSLK.mem
    val int_to_tslk_level : Expression.integer -> TSLK.level
    val formula_to_tslk_formula : Expression.formula -> TSLK.formula

    val sort_to_expr_sort : TSLK.sort -> Expression.sort
    val var_to_expr_var : TSLK.V.t -> Expression.V.t
    val tid_to_expr_tid : TSLK.tid -> Expression.tid
    val term_to_expr_term : TSLK.term -> Expression.term
    val set_to_expr_set : TSLK.set -> Expression.set
    val elem_to_expr_elem : TSLK.elem -> Expression.elem
    val addr_to_expr_addr : TSLK.addr -> Expression.addr
    val cell_to_expr_cell : TSLK.cell -> Expression.cell
    val setth_to_expr_setth : TSLK.setth -> Expression.setth
    val setelem_to_expr_setelem : TSLK.setelem -> Expression.setelem
    val path_to_expr_path : TSLK.path -> Expression.path
    val mem_to_expr_mem : TSLK.mem -> Expression.mem
    val level_to_expr_int : TSLK.level -> Expression.integer
    val formula_to_expr_formula : TSLK.formula -> Expression.formula

  end

