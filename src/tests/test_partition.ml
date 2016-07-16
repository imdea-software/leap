
(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)



module E = Expression

let _ =

  let var_i = E.build_global_var "insert_i_k_0" E.Int in
  let var_I2 = E.build_global_var "$Int_2" E.Int in
  let var_I1 = E.build_global_var "$Int_1" E.Int in
  let var_max = E.build_global_var "maxLevel" E.Int in
  let var_j = E.build_global_var "j" E.Int in

  let dom = [var_i; var_I2; var_I1; var_max; var_j] in

  let eq_list = [Partition.Eq (var_I1, var_max);
                 Partition.Eq (var_j, var_max);
                 Partition.Eq (var_I1, var_i);
                 Partition.Eq (var_I1, var_I2);
                 Partition.Eq (var_I1, var_j);
                 Partition.Eq (var_i, var_max)] in

  let ineq_list = [Partition.Ineq (var_i, var_I1)] in

  let order_list = [Partition.Ineq (var_i, var_j);
                    Partition.Ineq (var_max, var_j)] in

  
  (* let ps = Partition.gen_partitions E.V.to_str dom (eq_list @ ineq_list @ order_list) in *)
  let ps = Partition.gen_partitions dom (eq_list @ ineq_list @ order_list) in
  print_endline ("GENERATED PARTITIONS: " ^ (string_of_int (List.length ps)));
  List.iter (fun p -> print_endline (Partition.to_str E.V.to_str p)) ps;
