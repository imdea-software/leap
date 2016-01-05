type t

type rule_t
type case_t
type case_tbl_t
type axiom_tbl_t

val empty_axioms : unit -> t
val new_axioms : rule_t list -> t
val new_axiom_table : Tag.tag_table -> axiom_tbl_t
val new_rule : Tag.f_tag -> case_t list -> rule_t
val new_case : Expression.pc_t -> Tag.f_tag list -> case_t

val axiom_table_to_str : axiom_tbl_t -> string

val lookup : t -> Tag.f_tag -> Expression.pc_t -> Tag.f_tag list

val apply : axiom_tbl_t -> Expression.formula -> Tag.f_tag -> Expression.formula

