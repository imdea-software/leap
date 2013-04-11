module Arr = Arrangements

let _ =
  let arr = Arr.empty () in
  Arr.add_elem arr "A";
  Arr.add_elem arr "B";
  Arr.add_elem arr "C";
  Arr.add_eq arr "A" "B";
  Arr.add_ineq arr "B" "C";
  Arr.add_lesseq arr "B" "C";
  (* Generate arrangement tree list *)
  let tree_list = Arr.gen_arrtrees arr in
  (* Print generated arrangement trees *)
  List.iter (fun t -> print_endline (Arr.arrtree_to_str (fun x->x) t)) tree_list;

  (* Generate arrangements as lists *)
  let gen_arrs = Arr.gen_arrs arr in
  (* Print generated arrangement lists. Hopefully, they should be the same =) *)
  print_endline (Arr.arrtree_set_to_str (fun x->x) gen_arrs)
