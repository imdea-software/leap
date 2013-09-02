
exception SAT_Not_Found of string


let check_installed () : unit =
  match Unix.system ("minisat --help &> /dev/null") with
  | Unix.WEXITED 0 -> ()
  | _ -> raise(SAT_Not_Found "minisat")
