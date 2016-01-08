{
open IGraphParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' '_']
let alphanumext = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' '_' '-']
let alphanum_not_prime = ['A'-'Z' 'a'-'z' '0'-'9' '/' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | 'S'                         { Global.last "S"                 ; SELF_PREMISE }
  | 'O'                         { Global.last "O"                 ; OTHERS_PREMISE }
  | 'I'                         { Global.last "I"                 ; COND_INITIATION }
  | 'C'                         { Global.last "C"                 ; COND_CONSECUTION }
  | 'A'                         { Global.last "A"                 ; COND_ACCEPTANCE }
  | 'F'                         { Global.last "F"                 ; COND_FAIRNESS }
  | "forall"                    { Global.last "FORALL"            ; AXIOM_FORALL }
  | "->"                        { Global.last "->"                ; SEQ_ARROW }
  | "=>"                        { Global.last "=>"                ; CONC_ARROW }
  | ','                         { Global.last ","                 ; COMMA }
  | ':'                         { Global.last ":"                 ; COLON }
  | "::"                        { Global.last "::"                ; DOUBLECOLON }
  | ';'                         { Global.last ";"                 ; SEMICOLON }
  | '['                         { Global.last "["                 ; OPEN_BRACK }
  | ']'                         { Global.last "]"                 ; CLOSE_BRACK }
  | '{'                         { Global.last "{"                 ; OPEN_BRACE }
  | '}'                         { Global.last "}"                 ; CLOSE_BRACE }
  | '('                         { Global.last "("                 ; OPEN_PAREN }
  | ')'                         { Global.last ")"                 ; CLOSE_PAREN }
  | '|'                         { Global.last "|"                 ; BAR }
  | "Tactics"                   { Global.last "Tactics"           ; TACTICS }
  | "Facts"                     { Global.last "Facts"             ; FACTS }
  | "union"                     { Global.last "union"             ; SMP_UNION }
  | "pruning"                   { Global.last "pruning"           ; SMP_PRUNING }
  | "dnf"                       { Global.last "dnf"               ; SMP_DNF }
  | (digit+) as num             { Global.last num                 ; NUMBER (int_of_string num) }
  | (letter alphanumext*) as id { Global.last id                  ; IDENT (id,Global.get_linenum()) }
  | whitespc                    { Global.last "whitespc"          ; norm lexbuf }
  | '\n'                        { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof                         { Global.last "EOF"; EOF }
  | _ as x                      { Global.last (String.make 1 x);
                                    print_endline ("Bad token: " ^ (String.make 1 x));
                                    raise(LexerError)
                                }
