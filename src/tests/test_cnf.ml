module PE = PosExpression

let _ =
  let phi = PE.And (PE.Pred"A", PE.Or(PE.Pred"B", PE.Pred"C")) in
  let cnf_phi = PE.disj_list (List.map PE.conj_list (PE.cnf phi)) in
  let dnf_phi = PE.conj_list (List.map PE.disj_list (PE.dnf phi)) in
  Printf.printf "Original formula: %s\n" (PE.expr_to_str phi);
  Printf.printf "CNF formula: %s\n" (PE.expr_to_str cnf_phi);
  Printf.printf "DNF formula: %s\n" (PE.expr_to_str dnf_phi);
  
  let phi = PE.Or (PE.Pred"A", PE.And(PE.Pred"B", PE.Pred"C")) in
  let cnf_phi = PE.disj_list (List.map PE.conj_list (PE.cnf phi)) in
  let dnf_phi = PE.conj_list (List.map PE.disj_list (PE.dnf phi)) in
  Printf.printf "Original formula: %s\n" (PE.expr_to_str phi);
  Printf.printf "CNF formula: %s\n" (PE.expr_to_str cnf_phi);
  Printf.printf "DNF formula: %s\n" (PE.expr_to_str dnf_phi)
  
