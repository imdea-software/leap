{
open Global
open TrsParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' ]
let alphanum_not_prime = ['A'-'Z' 'a'-'z' '0'-'9' '/' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | "Invariant"   { Global.last "invariant"   ; INVARIANT }
  | "@"           { Global.last "@"           ; AT }
  | "loc"         { Global.last "loc"         ; LOC }
  | "TRUE"        { Global.last "true"        ; TRUE }
  | "FALSE"       { Global.last "false"       ; FALSE }
  | '&'           { Global.last "&"           ; LOGICAL_AND }
  | '+'           { Global.last "+"           ; MATH_PLUS }
  | '-'           { Global.last "-"           ; MATH_MINUS }
  | '*'           { Global.last "*"           ; MATH_MULT }
  | '/'           { Global.last "/"           ; MATH_DIV }
  | "=="          { Global.last "=="          ; EQUALS }
  | "<="          { Global.last "<="          ; LESS_EQ }
  | ">="          { Global.last ">="          ; GREATER_EQ }
  | '('           { Global.last "("           ; OPEN_PAREN }
  | ')'           { Global.last ")"           ; CLOSE_PAREN }
  | '_'           { Global.last "_"           ; UNDERSCORE }
  | "__"          { Global.last "__"          ; DOUBLE_UNDERSCORE }
  | '''           { Global.last "'"           ; PRIME }
  | (_+)"ANSWER:" { Global.last "ANSWER"      ; ANSWER }
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letter alphanum_not_prime*) as id
        { Global.last id; IDENT (id,Global.get_linenum()) }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise LexerError
                      }
