
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

  let uf = LeapUnionFind.empty () in

  let var_t = E.build_global_var "t" E.Int in
  let var_v = E.build_global_var "v" E.Int in
  let var_a = E.build_global_var "a" E.Int in
  let var_b = E.build_global_var "b" E.Int in
  let var_c = E.build_global_var "c" E.Int in

  LeapUnionFind.add_new uf var_c;
  LeapUnionFind.add_new uf var_v;
  LeapUnionFind.union uf var_t var_a;
  LeapUnionFind.union uf var_v var_b;
  LeapUnionFind.union uf var_a var_b;

  print_endline (LeapUnionFind.to_str E.V.to_str uf);

  let sets = LeapUnionFind.gen_sets uf in
  print_endline "Generated sets:";
  List.iter (fun s ->
    print_endline (LeapGenericSet.to_str E.V.to_str s)
  ) sets
  
