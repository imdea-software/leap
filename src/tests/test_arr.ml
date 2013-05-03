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

(*
  Arr.add_elem arr "B";
  Arr.add_elem arr "A";
  Arr.add_elem arr "C";
  Arr.add_less arr "A" "B";
*)

  Arr.add_elem arr "1";
  Arr.add_elem arr "2";
  Arr.add_elem arr "3";
  Arr.add_elem arr "4";
  Arr.add_elem arr "5";
  Arr.add_elem arr "6";
  Arr.add_elem arr "7";
  Arr.add_elem arr "8";
  Arr.add_elem arr "9";
  Arr.add_elem arr "10";
  Arr.add_elem arr "11";
  Arr.add_elem arr "12";
  Arr.add_elem arr "13";
  Arr.add_elem arr "14";
  Arr.add_elem arr "15";
  Arr.add_elem arr "16";
  Arr.add_elem arr "17";
  Arr.add_elem arr "18";
  Arr.add_elem arr "19";
  Arr.add_elem arr "20";
  Arr.add_elem arr "21";
  Arr.add_elem arr "22";
  Arr.add_elem arr "23";

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
