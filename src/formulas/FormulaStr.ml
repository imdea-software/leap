module type S =
  sig
    type atom

    val literal_to_str : atom Formula.literal -> string
    val conjunctive_formula_to_str : atom Formula.conjunctive_formula -> string
    val disjunctive_formula_to_str : atom Formula.disjunctive_formula -> string
    val formula_to_str : atom Formula.formula -> string
  end


module Make (AStr : AtomStr.S) =
  struct

    module F = Formula

    type atom = AStr.t

    (* Operation for pretty printing *)
    type logic_op_t = AndOp | OrOp | ImpliesOp | IffOp | NotOp | NoneOp


    (* Configuration *)
    let trueSym = "true"
    let falseSym = "false"
    let andSym = "/\\"
    let orSym = "\\/"
    let notSym = "~"
    let implSym = "->"
    let iffSym = "<>"


    let literal_to_str (l:atom F.literal) : string =
      match l with
      | F.Atom a -> AStr.atom_to_str a
      | F.NegAtom a  -> "(" ^notSym^ " " ^(AStr.atom_to_str a)^ ")"


    let concat_literals (ls:atom F.literal list) (sym:string) : string =
      match ls with
      | [] -> ""
      | l::[] -> literal_to_str l
      | x::xs -> List.fold_left (fun str l ->
                   str ^ " " ^ sym ^ " " ^ (literal_to_str l)
                 ) (literal_to_str x) xs


    let conjunctive_formula_to_str (cf:atom F.conjunctive_formula) : string =
      match cf with
      | F.TrueConj -> trueSym
      | F.FalseConj -> falseSym
      | F.Conj ls -> concat_literals ls andSym


    let disjunctive_formula_to_str (df:atom F.disjunctive_formula) : string =
      match df with
      | F.TrueDisj -> trueSym
      | F.FalseDisj -> falseSym
      | F.Disj ls -> concat_literals ls orSym


    let rec formula_to_str_aux (op:logic_op_t) (phi:atom F.formula) : string =
      match phi with
      | F.Literal l -> literal_to_str l
      | F.True -> trueSym
      | F.False -> falseSym
      | F.And(a,b)     -> let a_str = formula_to_str_aux AndOp a in
                          let b_str = formula_to_str_aux AndOp b in
                          if op = AndOp then
                            a_str ^ " " ^andSym^ " " ^ b_str
                          else
                            "(" ^ a_str ^ " " ^andSym^ " " ^ b_str ^ ")"
      | F.Or(a,b)      -> let a_str = formula_to_str_aux OrOp a in
                          let b_str = formula_to_str_aux OrOp b in
                          if op = OrOp then
                            a_str ^ " " ^orSym^ " " ^ b_str
                          else
                            "(" ^ a_str ^ " " ^orSym^ " " ^ b_str ^ ")"
      | F.Not a        -> let a_str = formula_to_str_aux NotOp a in
                          if op = NotOp then
                            notSym ^ " " ^ a_str
                          else
                            "(" ^notSym^ " " ^ a_str ^ ")"
      | F.Implies(a,b) -> let a_str = formula_to_str_aux ImpliesOp a in
                          let b_str = formula_to_str_aux ImpliesOp b in
                          if op = ImpliesOp then
                            a_str ^ " " ^implSym^ " " ^ b_str
                          else
                            "(" ^ a_str ^ " " ^implSym^ " " ^ b_str ^ ")"
      | F.Iff(a,b)     -> let a_str = formula_to_str_aux IffOp a in
                          let b_str = formula_to_str_aux IffOp b in
                          if op = IffOp then
                            a_str ^ " " ^iffSym^ " " ^ b_str
                          else
                            "(" ^ a_str ^ " " ^iffSym^ " " ^ b_str ^ ")"

    let formula_to_str (phi:atom F.formula) : string =
      formula_to_str_aux NoneOp phi

  end
