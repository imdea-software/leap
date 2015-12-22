type t

type rule_t
type case_t

val empty_axioms : unit -> t
val new_axioms : rule_t list -> t
val new_rule : Tag.f_tag -> case_t list -> rule_t
val new_case : Expression.pc_t -> Tag.f_tag list -> case_t
