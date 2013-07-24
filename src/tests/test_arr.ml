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
(*  Arr.add_less arr "int1" "maxLevel"; *)
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

(*
    Domain : {maxlevel;int1;int2;j;i_k0;lvl}
    Minimum: int1
    Eqs    : {i_k0=int1;i_k0=lvl}
    Ineqs  : {}
    Order  : {maxlevel<j;int1<maxlevel;lvl<maxlevel}
    <=     : {}
*)




  (* Arrangement representation *)
  print_endline (Arr.to_str arr (fun i -> i));

  (* Generate arrangement tree list *)
  let tree_list = Arr.gen_arrtrees (fun x -> x) arr in
  (* Print generated arrangement trees *)
  List.iter (fun t -> print_endline (Arr.arrtree_to_str (fun x->x) t)) tree_list;

  print_endline "Will show arrangements as lists";
  (* Generate arrangements as lists *)
  let gen_arrs = Arr.gen_arrs (fun x -> x) arr in
  (* Print generated arrangement lists. Hopefully, they should be the same =) *)
  print_endline (Arr.arrtree_set_to_str (fun x->x) gen_arrs);

  Arr.test arr (fun x -> x)
