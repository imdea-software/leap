
type fol_mode_t =
  | PCOnly
  | VarsOnly
  | PCVars

type 'var fol_ops_t =
  {
    fol_pc : bool;
    fol_var : 'var -> 'var;
  }

module type ExtendedExpressionInfo =
  sig
    type atom_t
  end

module type S =
  sig
    type atom
    type formula = atom Formula.formula

    val plain : fol_mode_t -> formula -> formula
  end


let plain (mode:fol_mode_t) (phi:'atom Formula.formula) : 'atom Formula.formula = phi
