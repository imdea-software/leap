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

  Arr.set_minimum arr (new_int "D");

  Arr.add_lesseq arr (new_int "C") (new_int "A");

  Arr.add_ineq arr (new_int "C") (new_int "D");

  Arr.add_less arr (new_int "A") (new_int "B");

  let ag = ArrGen.new_arr_gen arr in
  let next_arr = ref (ArrGen.next_arr ag) in
  while (!next_arr <> []) do
    let str = "[" ^ String.concat ";"
                (List.map (fun xs ->
                  "[" ^ (String.concat "," (List.map NE.integer_to_str xs)) ^ "]"
                 ) (!next_arr)) ^ "]" in
    print_endline str;
    next_arr := ArrGen.next_arr ag
  done;

