
module type S =
  sig
    type atom

    val literal_to_str : atom Formula.literal -> string
    val conjunctive_formula_to_str : atom Formula.conjunctive_formula -> string
    val disjunctive_formula_to_str : atom Formula.disjunctive_formula -> string
    val formula_to_str : atom Formula.formula -> string
  end


module Make (AStr : AtomStr.S) : S
  with type atom = AStr.t
