let filename = ref ""

let _ =
  Arg.parse [] (fun str -> filename := str) "";

  if !filename = "" then
    print_endline "No input file provided."
  else begin
    let cfg = SMTExecute.new_configuration SMTExecute.Z3 in
    SMTExecute.compute_model cfg true;
    let result = SMTExecute.run cfg (LeapFile.read !filename) in
(*    let model = SMTExecute.get_model() in *)
    print_endline ("ANSWER: " ^ (if Sat.is_sat result then "SAT" else "UNSAT"))
  end
