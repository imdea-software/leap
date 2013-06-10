{
open Global
open IGraphParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' '_']
let alphanum_not_prime = ['A'-'Z' 'a'-'z' '0'-'9' '/' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | 'S'                 {Global.last "S"                 ; SELF_PREMISE }
  | 'O'                 {Global.last "O"                 ; OTHERS_PREMISE }
  | "split-goal"        {Global.last "split-goal"        ; SUPP_SPLIT_GOAL_TACTIC }
  | "full"              {Global.last "full"              ; SUPP_FULL_TACTIC }
  | "reduce"            {Global.last "reduce"            ; SUPP_REDUCE_TACTIC }
  | "reduce2"           {Global.last "reduce2"           ; SUPP_REDUCE2_TACTIC }
  | "split-consequent"  {Global.last "split-consequent"  ; FORMULA_SPLIT_CONSEQUENT_TACTIC }
  | "simplify-pc"       {Global.last "simplify-pc"       ; FORMULA_SIMPLIFYPC_TACTIC }
  | "propagate"         {Global.last "propagate"         ; FORMULA_PROPAGATE_TACTIC }
  | "filter-strict"     {Global.last "filter-strict"     ; FORMULA_FILTER_TACTIC }
  | "->"                {Global.last "->"                ; SEQ_ARROW }
  | "=>"                {Global.last "=>"                ; CONC_ARROW }
  | "[]"                {Global.last "[]"                ; BOX }
  | ','                 {Global.last ","                 ; COMMA }
  | ':'                 {Global.last ":"                 ; COLON }
  | ';'                 {Global.last ";"                 ; SEMICOLON }
  | '['                 {Global.last "["                 ; OPEN_BRACK }
  | ']'                 {Global.last "]"                 ; CLOSE_BRACK }
  | '{'                 {Global.last "{"                 ; OPEN_BRACE }
  | '}'                 {Global.last "}"                 ; CLOSE_BRACE }
  | '('                 {Global.last "("                 ; OPEN_PAREN }
  | ')'                 {Global.last ")"                 ; CLOSE_PAREN }
  | '|'                 {Global.last "|"                 ; BAR }
  | "union"             {Global.last "union"             ; SMP_UNION }
  | "pruning"           {Global.last "pruning"           ; SMP_PRUNING }
  | "dnf"               {Global.last "dnf"               ; SMP_DNF }
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letter alphanum*) as id
        { Global.last id; IDENT (id,Global.get_linenum()) }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise(LexerError)
                      }
