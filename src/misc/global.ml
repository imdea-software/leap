exception ParserError of string

let linenum = ref 1

let lastt = ref "INIT"

let last str = lastt := str

let get_last () = !lastt

let reset_linenum () = linenum := 1

let incr_linenum () = incr linenum

let get_linenum () = !linenum

let pln () = print_endline (string_of_int !linenum)

let print_output_linenum ((n,_,l),_) = Printf.printf "Line %d: %s\n" l n 
