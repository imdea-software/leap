{
open Global
open YicesModelParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' '_']
let alphanum_not_prime = ['A'-'Z' 'a'-'z' '0'-'9' '/' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | '='                      {Global.last "="              ; EQUAL                                }
  | '('                      {Global.last "("              ; OPEN_PAREN                           }
  | ')'                      {Global.last ")"              ; CLOSE_PAREN                          }
  | '-'                      {Global.last "-"              ; MINUS                                }
  | "select"                 {Global.last "select"         ; SELECT                               }
  | "mk-record"              {Global.last "mk-record"      ; MK_RECORD                            }
  | ("tt_")(digit+ as id)    {Global.last ("tt_" ^ id)     ; TID_ELEM ("tt_" ^ id)                }
  | "NoThread"               {Global.last "NoThread"       ; NO_THREAD                            }
  | ("aa_")(digit+ as id)    {Global.last ("aa_" ^ id)     ; ADDR_ELEM ("aa_" ^ id)               }
  | ("ee_")(digit+ as id)    {Global.last ("ee_" ^ id)     ; ELEM_ELEM ("ee_" ^ id)               }
  | "error"                  {Global.last "error"          ; ERROR                                }
  | "null"                   {Global.last "null"           ; NULL                                 }
  | "::"                     {Global.last "next"           ; DOUBLE_COLON                         }
  | "true"                   {Global.last "true"           ; BOOL (true)                          }
  | "false"                  {Global.last "false"          ; BOOL (false)                         }
  | (digit+) as num          {Global.last num              ; NUMBER (int_of_string num)           }
  | (letter alphanum*) as id {Global.last id               ; IDENT (id,Global.get_linenum())      }
  | whitespc                 {Global.last "whitespc"       ; norm lexbuf                          }
  | '\n'                     {Global.last "\\n"            ; Global.incr_linenum (); norm lexbuf  }
  | eof                      {Global.last "EOF"            ; EOF                                  }
  | _ as x                   {Global.last (String.make 1 x);
                                print_endline ("Bad token: " ^ (String.make 1 x)); raise LexerError }
