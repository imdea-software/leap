
module type S =
  sig
    type atom
    type formula = atom Formula.formula

    include BasicExpression.S
      with type atom := atom
      with type formula := formula

    include ExtendedExpression.S
      with type atom := atom
      with type formula := formula
  end

