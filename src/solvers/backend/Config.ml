

let exec_path : string ref = ref ""


let get_exec_path () : string =
  if !exec_path = "" then
    let _ = exec_path := Filename.dirname (Unix.getenv "_")
    in
      !exec_path
  else
    !exec_path

