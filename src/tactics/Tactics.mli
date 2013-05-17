
type solve_tactic_t = Cases

type pre_tac_t = Full | Reduce | Reduce2

type post_tac_t = SplitConseq | SimplPCVoc


type t

type support_info_t

type task_t

type res_info_t

(* res_info_t functions *)
val try_pos : res_info_t -> bool

(* Describing tactics *)
val new_tactics : Smp.cutoff_strategy_t option ->
                  solve_tactic_t option ->
                  pre_tac_t list ->
                  post_tac_t list ->
                  t

val smp_cutoff : t -> Smp.cutoff_strategy_t option
val solve_tactic : t -> solve_tactic_t option
val pre_tacs : t -> pre_tac_t list
val post_tacs : t -> post_tac_t list


val supp_voc : support_info_t -> Expression.tid list
val supp_list : support_info_t -> Expression.formula list
val extra_supp_list : support_info_t -> Expression.formula list
val diff_conj : support_info_t -> Expression.formula

val supp_fresh_tid : support_info_t -> Expression.tid

val specialize_tacs : t -> t -> t



(* Provisional tactics... to be unified *)

val simplify_with_pc : Expression.formula ->
                       Expression.tid ->
                       int list ->
                       bool ->
                       Expression.formula

val simplify_with_vocabulary : Expression.formula ->
                               Expression.variable list ->
                               Expression.formula

(*
val apply_tactics : Expression.formula list ->
                    Expression.formula ->
                    Expression.formula_info_t ->
                    Expression.tid option ->
                    t ->
                    Expression.formula list
*)

val gen_support : Expression.formula list ->
                  Expression.tid list ->
                  pre_tac_t list ->
                  support_info_t


val new_task : Expression.formula list ->
               Expression.formula option ->
               Expression.formula ->
               Expression.formula_info_t ->
               Expression.tid list ->
               Expression.tid ->
               Expression.pc_t ->
               task_t


val apply_post_tacs : task_t list -> post_tac_t list -> bool ->
                      (Expression.formula * res_info_t) list 
