

type cond_effect_t = Expression.formula * (* Condition list *)
                     Expression.formula * (* Term - Expression assignment *)
                     Expression.pc_t    * (* Current program counter *)
                     Expression.pc_t      (* Next program counter *)


type malloc_info =
  {
    tids       : Expression.tid list;
    gAddrs     : Expression.variable list;
    gSets      : Expression.variable list;
    lAddrs     : Expression.variable list;
    lSets      : Expression.variable list;
  }


type prog_type = Num | Heap



val construct_stm_term_eq : malloc_info ->
                            prog_type ->
                            Statement.term ->
                            Expression.shared_or_local ->
                            Statement.expr_t ->
                            (Expression.term list * Expression.formula)



val construct_stm_term_eq_as_array : malloc_info ->
                                     prog_type ->
                                     Statement.term ->
                                     Expression.shared_or_local ->
                                     Statement.expr_t ->
                                     (Expression.term list * Expression.formula)


val gen_st_cond_effect : prog_type ->
                         Statement.statement_t ->
                         bool ->
                         cond_effect_t list


val gen_st_cond_effect_as_array : prog_type ->
                                  Statement.statement_t ->
                                  bool ->
                                  Expression.shared_or_local ->
                                  cond_effect_t list
