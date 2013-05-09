module Arr = Arrangements

let _ =
  let arr = Arr.empty true in
(*
  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "int3";
  Arr.add_elem arr "i";
  Arr.add_elem arr "maxLevel";
  Arr.add_eq arr "int3" "i+1";
  Arr.add_eq arr "int1" "0";
  
  Arr.add_lesseq arr "int1" "maxLevel";
*)
(*  Arr.add_less arr "int1" "maxLevel"; *)


  Arr.add_elem arr "B";
  Arr.add_elem arr "A";
  Arr.add_elem arr "C";
(*  Arr.add_less arr "A" "B"; *)
(*  Arr.set_minimum arr "B"; *)

(*
  Arr.add_lesseq arr "B" "A";
  Arr.add_lesseq arr "B" "C";
*)

(*
  Arr.add_eq arr "B" "C";
  Arr.add_less arr "B" "A";
*)

(*
  Arr.add_eq arr "B" "C";
  Arr.add_eq arr "B" "A";
*)
(*
  Arr.add_lesseq arr "B" "C";
  Arr.add_lesseq arr "B" "A";
*)
  Arr.set_minimum arr "B";


(*
  Arr.add_eq arr "B" "A";
  Arr.add_less arr "B" "C";
*)


(*  Arr.add_lesseq arr "B" "A";
  Arr.add_lesseq arr "B" "C";
*)
(*  Arr.set_minimum arr "B"; *)


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
  print_endline (Arr.arrtree_set_to_str (fun x->x) gen_arrs)
