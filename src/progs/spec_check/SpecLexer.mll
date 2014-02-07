{
open Global
open SpecParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '_' '/' ''' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | '('           { Global.last "("           ; OPEN_PAREN }
  | ')'           { Global.last ")"           ; CLOSE_PAREN }
  | '='           { Global.last "="           ; EQUALS }
  | "!="          { Global.last "!="          ; NOT_EQUALS }
  | "/\\"         { Global.last "/\\"         ; LOGICAL_AND }
  | "and"         { Global.last "and"         ; LOGICAL_AND }
  | "\\/"         { Global.last "\\/"         ; LOGICAL_OR  }
  | "or"          { Global.last "or"          ; LOGICAL_OR  }
  | "->"          { Global.last "->"          ; LOGICAL_THEN }
  | "<->"         { Global.last "<->"         ; LOGICAL_IFF }
  | '~'           { Global.last "~"           ; LOGICAL_NOT }
  | "true"        { Global.last "true"        ; LOGICAL_TRUE }
  | "false"       { Global.last "false"       ; LOGICAL_FALSE }
  | ':'           { Global.last ":"           ; COLON }
  | '+'           { Global.last "+"           ; MATH_PLUS }
  | '-'           { Global.last "-"           ; MATH_MINUS }
  | '*'           { Global.last "*"           ; MATH_MULT }
  | '/'           { Global.last "/"           ; MATH_DIV }
  | '<'           { Global.last "<"           ; MATH_LESS }
  | '>'           { Global.last ">"           ; MATH_GREATER }
  | "<="          { Global.last "<="          ; MATH_LESS_EQ }
  | ">="          { Global.last ">="          ; MATH_GREATER_EQ }
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letter alphanum*) as id { Global.last id; IDENT (id,Global.get_linenum()) }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise(LexerError)
                      }
