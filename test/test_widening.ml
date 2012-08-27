(****************)
(* ARGS         *)
(****************)

open Printf

open LeapLib
open Global

module Expr = Expression
module NumExpr = NumExpression


exception MoreThanTwoInputFiles
exception No_file
exception File_not_found of string

let assignopt valref valbool aval =  valref := aval ; valbool := true

let input_file_one = ref ""
let is_input_file_one = ref false
let input_file_one_fd : Unix.file_descr ref = ref Unix.stdin

let input_file_two = ref ""
let is_input_file_two = ref false
let input_file_two_fd : Unix.file_descr ref = ref Unix.stdin

(* Program arguments *)
let verbose            = ref false

let assignopt s opt opt_flag = opt := s ; opt_flag := true
let assigninputfileone s = assignopt s input_file_one is_input_file_one
let assigninputfiletwo s = assignopt s input_file_two is_input_file_two

(* Program arguments *)

let set_debug i = Debug._debug_ := true;
                  Debug._debug_level_ := i


module MyArgs =
  struct
    let myopts =
      [ ("-v",      Arg.Set verbose,"verbose");
        ("--debug", Arg.Int set_debug, "debug level")
      ]
    let anon_fun str = 
      if not !is_input_file_one then 
  begin assigninputfileone str end
      else if not !is_input_file_two then
  begin assigninputfiletwo str end
      else  raise(MoreThanTwoInputFiles)

    let usagemsg = "Reads two numerical conjuncts from two files and generates their widening."
    let error msg = Arg.usage myopts msg ; exit 0

    let simple_error msg = Printf.printf "%s\n" msg ; exit 0

    let postcheck () = ()

  end


let parse_args _ = Arg.parse MyArgs.myopts MyArgs.anon_fun MyArgs.usagemsg ;
                   MyArgs.postcheck ()



let open_input name flag fd  =
  if !flag then
    begin
      fd := Unix.openfile !name [Unix.O_RDONLY] 0 ;
      Unix.in_channel_of_descr !fd
    end
  else
    raise No_file
    (*stdin*)

let open_input_one _ = open_input input_file_one is_input_file_one input_file_one_fd
let open_input_two _ = open_input input_file_two is_input_file_two input_file_two_fd


let close_input_one _ =
  if !is_input_file_one then Unix.close !input_file_one_fd
let close_input_two _ =
  if !is_input_file_two then Unix.close !input_file_two_fd


(****************)
(* main         *)
(****************)

let read_formula ch =
  let lexer = Lexing.from_channel ch in
  let rec flist_to_int_formula xfl =
    match xfl with
  [] -> NumExpr.True
      | x::xs -> NumExpr.And(NumExpr.formula_to_int_formula x,flist_to_int_formula xs)
  in 
  let x_fl = Trsparser.conj_list Trslexer.norm lexer in
  let phi = flist_to_int_formula x_fl in
    phi


let read_formula_one _ =
  let ch  = open_input_one () in
  let x   = read_formula ch in
  let _   = close_input_one () in
    x

let read_formula_two _ =
  let ch  = open_input_two () in
  let y   = read_formula ch in
  let _   = close_input_two () in
    y


let _ =
  try
    let _   = parse_args () in
    let x   = read_formula_one () in
    let y   = read_formula_two () in
    let phi_out = Yices.standard_widening x y in
      Printf.printf "===\n%s===\n" (NumExpr.int_formula_to_string phi_out) ;
  with
    | Global.ParserError msg -> Interface.Err.msg "Parsing error" msg
    | Parsing.Parse_error -> Interface.Err.msg "Parsing error" $
        sprintf "Unexpected symbol \"%s\" at line %i" (Global.get_last()) (Global.get_linenum())
    | e -> raise e


