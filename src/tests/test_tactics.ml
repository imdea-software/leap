module E = Expression

let _ =
  let v1 = E.build_var "A" E.Int false E.V.Shared E.V.GlobalScope E.RealVar in
  let ante = [E.eq_int (E.VarInt v1) (E.IntVal 42)] in

  let imp = {
             Tactics.ante = E.conj_list ante;
             Tactics.conseq = E.False
            } in
  Printf.printf "Old antecedent: %s\n" (E.formula_to_str imp.Tactics.ante);
  Printf.printf "Old consequent: %s\n" (E.formula_to_str imp.Tactics.conseq);
  let new_imp = Tactics.tactic_simplify_pc imp in
  Printf.printf "New antecedent: %s\n" (E.formula_to_str new_imp.Tactics.ante);
  Printf.printf "New consequent: %s\n" (E.formula_to_str new_imp.Tactics.conseq)
  

