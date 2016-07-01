module Arr = Arrangements
module ArrGen = NumArrangementGenerator
module NE = NumExpression

let new_int (id:string) : NE.integer =
  NE.Var (NE.build_var id NE.Int false NE.V.Shared NE.V.GlobalScope)

let _ =
  let arr = Arr.empty true in

  Arr.clear arr;

  Arr.add_elem arr (new_int "A");
  Arr.add_elem arr (new_int "B");
  Arr.add_elem arr (new_int "C");
  Arr.add_elem arr (new_int "D");

  Arr.add_ineq arr (new_int "C") (new_int "D");

  Arr.add_less arr (new_int "A") (new_int "B");

  
  (* Arrangement representation *)
  print_endline (Arr.to_str arr NE.integer_to_str);

  (* Generate arrangement tree list *)
  let tree_list = Arr.gen_arrtrees arr in
  (* Print generated arrangement trees *)
  List.iter (fun t -> print_endline (Arr.arrtree_to_str NE.integer_to_str t)) tree_list;

  print_endline "Will show arrangements as lists";
  (* Generate arrangements as lists *)
  let gen_arrs = Arr.gen_arrs arr in
  (* Print generated arrangement lists. Hopefully, they should be the same =) *)
  print_endline (Arr.arrtree_set_to_str NE.integer_to_str gen_arrs);
  
(*
  let ag = ArrGen.new_arr_gen arr in
  let next_arr = ref (ArrGen.next_arr ag) in
  while (!next_arr <> []) do
    let str = "[" ^ String.concat ";" (List.map (fun xs -> "[" ^ (String.concat "," (List.map NE.integer_to_str xs)) ^ "]" ) (!next_arr)) ^ "]" in
    print_endline str;
    next_arr := ArrGen.next_arr ag
  done;
*)
  print_endline "Final test";

  Arr.test arr NE.integer_to_str

