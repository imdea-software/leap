(* Interface.ml *)


module File =
struct
  let readFile (fileName:string) : string =
    let ic = open_in fileName in
    let n = in_channel_length ic in
    let s = String.create n in
      really_input ic s 0 n;
      close_in ic;
      (s)


  let writeFile (fileName:string) (str:string) : unit =
    let oc = open_out fileName in
    let _ = Printf.fprintf oc "%s" str in
      close_out oc


  let readChannel (ch:Pervasives.in_channel) : string =
    let result = ref "" in
    let rec read _ = try
                       let str = Pervasives.input_line ch in
                       let _ = result := !result ^ str ^ "\n"
                       in
                         read ()
                     with
                     | End_of_file -> Unix.close_process_in ch in
    let _ = read ()
    in
      !result
  

end


module Err =
struct

  let msg (title:string) (info:string) =
    Printf.eprintf "\n**** %s ****\n\n%s\n\n" title info


  let smsg (title:string) (info:string) =
    Printf.eprintf "**** %s: %s ****\n" title info

end
