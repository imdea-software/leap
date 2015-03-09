let _ =
  let filename = Sys.argv.(1) in
  print_endline ("Going to parse file: " ^  filename);
  let input_channel = Pervasives.open_in filename in
  let model = (YicesModelParser.generic_model YicesModelLexer.norm)
                (Lexing.from_channel input_channel) in
  print_endline "Parsing done...";
  print_endline (GenericModel.model_to_str model);
  print_endline "Done"
