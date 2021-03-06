
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


module Arr = Arrangements

let _ =
  let arr = Arr.empty true in



  (** Example 1 **)
(*
  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "int3";
  Arr.add_elem arr "i";
  Arr.add_elem arr "maxLevel";
  Arr.add_eq arr "int3" "i+1";
  Arr.add_eq arr "int1" "0";
  
  Arr.add_lesseq arr "int1" "maxLevel";
  (* Arr.add_less arr "int1" "maxLevel"; *)
*)



  (** Example 2 **)
(*
  Arr.add_elem arr "B";
  Arr.add_elem arr "A";
  Arr.add_elem arr "C";
  Arr.set_minimum arr "B";
*)



  (** Example 3 **)
(*
  Arr.add_less arr "A" "B";
  Arr.set_minimum arr "B";
  Arr.add_lesseq arr "B" "A";
  Arr.add_lesseq arr "B" "C";
  Arr.add_eq arr "B" "C";
  Arr.add_less arr "B" "A";
  Arr.add_eq arr "B" "C";
  Arr.add_eq arr "B" "A";
  Arr.add_lesseq arr "B" "C";
  Arr.add_lesseq arr "B" "A";
  Arr.add_eq arr "B" "A";
  Arr.add_less arr "B" "C";
  Arr.add_lesseq arr "B" "A";
  Arr.add_lesseq arr "B" "C";
  Arr.set_minimum arr "B";
*)


  (** Example 4 **)
(*
  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "i_k0";
  Arr.add_elem arr "j";
  Arr.add_elem arr "maxlevel";
  Arr.add_elem arr "lvl";

  Arr.set_minimum arr "int1";
  Arr.add_eq arr "i_k0" "int1";
  Arr.add_less arr "i_k_0" "int2";
  Arr.add_less arr "maxlevel" "j";
  Arr.add_lesseq arr "int1" "maxlevel";

  Arr.add_lesseq arr "lvl" "maxlevel";
  Arr.add_lesseq arr "i_k0" "lvl";
*)


  (** Example 5 **)
(*
  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "i_k0";
  Arr.add_elem arr "j";
  Arr.add_elem arr "maxlevel";
  Arr.add_elem arr "lvl";

  Arr.set_minimum arr "int1";

  Arr.add_eq arr "i_k0" "int1";
  Arr.add_eq arr "i_k0" "lvl";
  Arr.add_eq arr "int1" "maxlevel";

  Arr.add_less arr "maxlevel" "j";
  Arr.add_less arr "lvl" "maxlevel";
*)
(*
    Domain : {maxlevel;int1;int2;j;i_k0;lvl}
    Minimum: int1
    Eqs    : {i_k0=int1;i_k0=lvl;int1=maxlevel}
    Ineqs  : {}
    Order  : {maxlevel<j;lvl<maxlevel}
    <=     : {}
*)


  (** Example 6 **)
(*
  Arr.clear arr;
  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "i_k0";
  Arr.add_elem arr "j";
  Arr.add_elem arr "maxlevel";
  Arr.add_elem arr "lvl";

  Arr.set_minimum arr "int1";

  Arr.add_eq arr "i_k0" "int1";
  Arr.add_eq arr "i_k0" "lvl";
  Arr.add_eq arr "int1" "lvl";


  Arr.add_less arr "maxlevel" "j";
  Arr.add_less arr "int1" "maxlevel";
  Arr.add_less arr "lvl" "maxlevel";
*)

(*
    Domain : {maxlevel;int1;int2;j;i_k0;lvl}
    Minimum: int1
    Eqs    : {i_k0=int1;i_k0=lvl}
    Ineqs  : {}
    Order  : {maxlevel<j;int1<maxlevel;lvl<maxlevel}
    <=     : {}
*)

  (** Example 7 **)
(*
  Arr.clear arr;
  Arr.add_elem arr "A";
  Arr.add_elem arr "B";
  Arr.add_elem arr "C";

  Arr.add_followed_by arr "A" "B";
*)


  (** Example 8 **)
(*
  Arr.clear arr;

  Arr.add_elem arr "int3";
  Arr.add_elem arr "i";
  Arr.add_elem arr "i_prime";
  Arr.add_elem arr "int1";
(*  Arr.add_elem arr "int2"; *)
(*  Arr.add_elem arr "j"; *)
(*  Arr.add_elem arr "maxLevel"; *)

(*  Arr.set_minimum arr "int2"; *)

(*  Arr.add_less arr "i" "i_prime"; *)
  Arr.add_less arr "i" "int3";
(*  Arr.add_less arr "i_prime" "maxLevel"; *)
  Arr.add_less arr "int1" "i";

(*  Arr.add_lesseq arr "int2" "maxLevel"; *)

  Arr.add_followed_by arr "i" "i_prime";
(*  Arr.add_followed_by arr "i" "int3"; *)
(*  Arr.add_followed_by arr "int1" "i"; *)
*)

(*
    Domain : {$int_3;insert_i_k_0;insert_i_prime_k_0;$int_1;$int_2;j;maxLevel}
    Minimum: $int_2
    Eqs    : {}
    Ineqs  : {}
    Order  : {insert_i_k_0<insert_i_prime_k_0;insert_i_k_0<$int_3;insert_i_prime_k_0<maxLevel;$int_1<insert_i_k_0}
    <=     : {$int_2<=maxLevel}
    succ   : {insert_i_k_0->insert_i_prime_k_0;insert_i_k_0->$int_3;$int_1->insert_i_k_0}
*)


  (** Example 9 **)
(*
  Arr.clear arr;

  Arr.add_elem arr "D";
  Arr.add_elem arr "B";
  Arr.add_elem arr "C";
  Arr.add_elem arr "A";

  Arr.add_less arr "B" "D";
  Arr.add_less arr "A" "B";

  Arr.add_followed_by arr "B" "C";
*)


  (** Example 10 **)

  Arr.clear arr;


  Arr.add_elem arr "$int2";
  Arr.add_elem arr "$int1";
  Arr.add_elem arr "insert::i";
  Arr.add_elem arr "j";
  Arr.add_elem arr "max";

  Arr.set_minimum arr "$int1";

  Arr.add_ineq arr "insert::i" "$int1";

  Arr.add_less arr "insert::i" "j";
  Arr.add_less arr "max" "j";

  Arr.add_lesseq arr "j" "max";
  Arr.add_lesseq arr "insert::i" "max";


  (* Arrangement representation *)
  print_endline (Arr.to_str arr (fun i -> i));

  (* Generate arrangement tree list *)
  let tree_list = Arr.gen_arrtrees arr in
  (* Print generated arrangement trees *)
  List.iter (fun t -> print_endline (Arr.arrtree_to_str (fun x->x) t)) tree_list;

  print_endline "Will show arrangements as lists";
  (* Generate arrangements as lists *)
  let gen_arrs = Arr.gen_arrs arr in
  (* Print generated arrangement lists. Hopefully, they should be the same =) *)
  print_endline (Arr.arrtree_set_to_str (fun x->x) gen_arrs);

  print_endline "Final test";

  Arr.test arr (fun x -> x)
