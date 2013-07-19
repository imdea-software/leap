let logFile : string ref = ref ""

let out : Pervasives.out_channel ref = ref Pervasives.stdout


let set_logFile (fileName:string) : unit =
  if fileName <> "" then begin
    logFile := fileName;
    out := Pervasives.open_out fileName
  end


let get_logFile () : string =
  !logFile


let is_set () : bool =
  !logFile <> ""


let close () : unit =
  if is_set() then Pervasives.close_out !out


let print (label:string) (str:string) : unit =
  if is_set() then begin
    let label_str = match label with
                    | "" -> ""
                    | _  -> "** " ^ label ^ ": " in
    Pervasives.output_string !out (label_str ^ str ^ "\n");
    Pervasives.flush !out
  end


let print_ocaml (str:string) : unit =
  print "ocaml" str


let print_cfg (str:string) : unit =
  print "prog configuration" str
