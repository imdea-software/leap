module type S =
  sig
    val plain : ExtendedExpression.fol_mode_t -> 'atom Formula.formula -> 'atom Formula.formula
  end

module Make (TK:Toolkit) : S
