module Arr = Arrangements

let _ =
  let arr = Arr.empty () in

  Arr.add_elem arr "int1";
  Arr.add_elem arr "int2";
  Arr.add_elem arr "int3";
  Arr.add_elem arr "i";
  Arr.add_elem arr "maxLevel";
  Arr.add_eq arr "int3" "i+1";
  Arr.add_eq arr "int1" "0";
  Arr.add_lesseq arr "int1" "maxLevel";
(*  Arr.add_less arr "int1" "maxLevel"; *)

(*
  Arr.add_less arr "A" "B";
*)

  (* Arrangement representation *)
  print_endline (Arr.to_str arr (fun i -> i));

  (* Generate arrangement tree list *)
  let tree_list = Arr.gen_arrtrees arr in
  (* Print generated arrangement trees *)
  List.iter (fun t -> print_endline (Arr.arrtree_to_str (fun x->x) t)) tree_list;

  (* Generate arrangements as lists *)
  let gen_arrs = Arr.gen_arrs arr in
  (* Print generated arrangement lists. Hopefully, they should be the same =) *)
  print_endline (Arr.arrtree_set_to_str (fun x->x) gen_arrs)
