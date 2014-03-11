exception Undefined_tag of string
exception Duplicated_tag of string

type f_tag

val tag_id    : f_tag -> string
val master_id : f_tag -> string
val subtag_id : f_tag -> string
val new_tag     : string -> string -> f_tag

module TagSet : Set.S with type elt = f_tag

module type S =
  sig

    type formula
    type f_info
    type tag_table

    val new_info    : f_info

    val tag_table_new         : tag_table
    val tag_table_clear       : tag_table -> unit
    val tag_table_add         : tag_table ->
                                f_tag ->
                                formula ->
                                f_info ->
                                unit
    val tag_table_mem         : tag_table -> f_tag -> bool
    val tag_table_find        : tag_table -> f_tag -> formula * f_info
    val tag_table_get_formula : tag_table -> f_tag -> formula
    val tag_table_get_info    : tag_table -> f_tag -> f_info
    val tag_table_size        : tag_table -> int
  end

module Make (E : GenericExpression.S) : S
  with type formula = E.formula
