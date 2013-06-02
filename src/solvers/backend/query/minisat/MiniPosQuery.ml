open LeapLib
open Printf

module PE = PosExpression

let prog_lines : int ref = ref 0
(** The number of lines in the program *)

let set_prog_lines (n:int) : unit =
  prog_lines := n

let pos_expression_to_str (expr:PE.expression) : string =
  let id_count = ref 1 in
  let expr_map : (PE.expression, int) Hashtbl.t = Hashtbl.create 10 in
  let lookup (expr:PE.expression) : int =
    let (neg, e) = match expr with
                     PE.Not t -> (true , t   )
                   | _           -> (false, expr) in
    let es = match e with
               PE.Eq (e1,e2)    -> [PE.Eq(e1,e2); PE.Eq (e2,e1)]
             | PE.InEq (e1, e2) -> [PE.InEq(e1,e2); PE.InEq(e2, e1)]
             | _                   -> [e] in
    let id = if List.exists (Hashtbl.mem expr_map) es then
               (List.fold_left (fun id x ->
                 try
                   Hashtbl.find expr_map x
                 with
                   Not_found -> id
               ) (-1) es)
             else
               let i = !id_count in
               let _ = incr id_count in
               let _ = Hashtbl.add expr_map e i in i in
    let _ = assert (id >=0)
    in
      if neg then -id else id in
  let expand_form = PE.expand_pc_range expr in
  let expr_voc = PE.voc expr in
  (* All threads are at some location *)
  let some_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              some_pos_list := PE.PC (i,PE.Local t,false) :: !some_pos_list
            ) expr_voc
          done in
  let some_pos = PE.disj_list !some_pos_list in
  (* All threads are at an unique location *)
  let unique_pos_list = ref [] in
  let _ = for i=1 to !prog_lines do
            List.iter (fun t ->
              let not_pos = ref [] in
              let not_pos' = ref [] in
              let _ = for j=1 to !prog_lines do
                        if i!=j then
                          begin
                            not_pos := PE.Not(PE.PC(j,PE.Local t,false))
                                          :: !not_pos;
                            not_pos':= PE.Not(PE.PC(j,PE.Local t,true))
                                          :: !not_pos'
                          end
                      done in
              let no_other_pos = PE.conj_list !not_pos in
              let no_other_pos' = PE.conj_list !not_pos' in
              let impl = PE.Implies (PE.PC (i,PE.Local t,false),
                                        no_other_pos) in
              let impl' = PE.Implies (PE.PC (i,PE.Local t,true),
                                         no_other_pos')
              in
                unique_pos_list := impl :: impl' :: !unique_pos_list
            ) expr_voc
          done in
  let unique_pos = PE.conj_list !unique_pos_list in
  (* Compute CNF and translate to SAT *)
  let full_formula = PE.And (some_pos, PE.And(unique_pos, expand_form)) in
  let cnf_form = PE.cnf full_formula in
  let desc_str = sprintf "c SAT description for location reasoning \
                          on formula:\nc %s\n" (PE.expr_to_str full_formula) 
  in
  let _ = print_endline (desc_str) in
  let _ = print_endline (string_of_int (List.length cnf_form)) in
  let expr_str = List.fold_left (fun str xs ->
                   str ^ (String.concat " " $
                            List.map (fun t ->
                              string_of_int (lookup t)
                            ) xs)
                       ^ " 0\n"
                 ) "" cnf_form in
  let header_str = sprintf "p cnf %i %i\n" (Hashtbl.length expr_map)
                                           (List.length cnf_form)

  in
    desc_str ^ header_str ^ expr_str
