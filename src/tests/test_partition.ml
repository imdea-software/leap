
module E = Expression

let _ =

  let var_i = E.build_global_var "insert_i_k_0" E.Int in
  let var_I2 = E.build_global_var "$Int_2" E.Int in
  let var_I1 = E.build_global_var "$Int_1" E.Int in
  let var_max = E.build_global_var "maxLevel" E.Int in
  let var_j = E.build_global_var "j" E.Int in

  let dom = [var_i; var_I2; var_I1; var_max; var_j] in

  let eq_list = [
                 Partition.Eq (var_I1, var_I2);
                 Partition.Eq (var_I1, var_j);
                 Partition.Eq (var_i, var_max)] in

  let ineq_list = [Partition.Ineq (var_i, var_I1)] in

  let order_list = [Partition.Ineq (var_i, var_j);
                    Partition.Ineq (var_max, var_j)] in

  
  let ps = Partition.gen_partitions E.V.to_str dom (eq_list @ ineq_list @ order_list) in
  print_endline ("GENERATED PARTITIONS: " ^ (string_of_int (List.length ps)));
  List.iter (fun p -> print_endline (Partition.to_str E.V.to_str p)) ps;
  


(*

**PARTITION DOMAIN: insert_i_k_0; $Int_2; $Int_1; maxLevel; j; 
**EQ_LIST: 
**EQ: $Int_1 maxLevel
**EQ: j maxLevel
**EQ: $Int_1 insert_i_k_0
**EQ: $Int_1 $Int_2
**EQ: $Int_1 j
**EQ: insert_i_k_0 maxLevel
**INEQ_LIST: 
**INEQ: insert_i_k_0 $Int_1
**ORDER_LIST: 
**INEQ: insert_i_k_0 j
**INEQ: maxLevel j
*)


  print_endline "Hola mundo"
