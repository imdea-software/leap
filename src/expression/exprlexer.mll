{
open Global
open Exprparser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '_' '/' ''' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | "Support"       { Global.last "Support"       ; SUPPORT }
  | "Diagram"       { Global.last "Diagram"       ; DIAGRAM }
  | "begin"         { Global.last "begin"         ; BEGIN }
  | "end"           { Global.last "end"           ; END }
  | "Threads"       { Global.last "Threads"       ; THREADS }
  | "Boxes"         { Global.last "Boxes"         ; BOXES }
  | "Nodes"         { Global.last "Nodes"         ; NODES }
  | "Initial"       { Global.last "Initial"       ; INITIAL }
  | "Edges"         { Global.last "Edges"         ; EDGES }
  | "Acceptance"    { Global.last "Acceptance"    ; ACCEPTANCE }
  | "with"          { Global.last "with"          ; WITH }
  | "default"       { Global.last "default"       ; DEFAULT }
  | "invariant"     { Global.last "invariant"     ; INVARIANT }
  | "formula"       { Global.last "formula"       ; FORMULA }
  | "param"         { Global.last "param"         ; PARAM }
  | "error"         { Global.last "error"         ; ERROR }
  | "mkcell"        { Global.last "mkcell"        ; MKCELL }
  | "data"          { Global.last "data"          ; DATA }
  | "next"          { Global.last "next"          ; NEXT }
  | "firstlocked"   { Global.last "fistlocked"    ; FIRSTLOCKED }
  | "lockid"        { Global.last "lockid"        ; LOCKID }
  | "lock"          { Global.last "lock"          ; LOCK }
  | "unlock"        { Global.last "unlock"        ; UNLOCK }
  | "rd"            { Global.last "rd"            ; MEMORY_READ }
  | "null"          { Global.last "null"          ; NULL }
  | "lowestElem"    { Global.last "lowestElem"    ; LOWEST_ELEM }
  | "highestElem"   { Global.last "highestElem"   ; HIGHEST_ELEM }
  | "upd"           { Global.last "upd"           ; UPDATE }
  | "epsilon"       { Global.last "epsilon"       ; EPSILON }
  | "EmptySet"      { Global.last "EmptySet"      ; EMPTYSET }
  | "Union"         { Global.last "Union"         ; UNION }
  | "Intr"          { Global.last "Intr"          ; INTR }
  | "SetDiff"       { Global.last "SetDiff"       ; SETDIFF } 
  | "EmptySetTh"    { Global.last "EmptySetTh"    ; EMPTYSETTH }
  | "SingleTh"      { Global.last "SingleTh"      ; SINGLETH }
  | "UnionTh"       { Global.last "UnionTh"       ; UNIONTH }
  | "IntrTh"        { Global.last "IntrTh"        ; INTRTH }
  | "SetDiffTh"     { Global.last "SetDiffTh"     ; SETDIFFTH }
  | "EmptySetInt"   { Global.last "EmptySetInt"   ; EMPTYSETINT }
  | "SingleInt"     { Global.last "SingleInt"     ; SINGLEINT }
  | "UnionInt"      { Global.last "UnionInt"      ; UNIONINT }
  | "IntrInt"       { Global.last "IntrInt"       ; INTRINT }
  | "SetDiffInt"    { Global.last "SetDiffInt"    ; SETDIFFINT }
  | "EmptySetElem"  { Global.last "EmptySetElem  "; EMPTYSETELEM }
  | "SingleElem"    { Global.last "SingleElem"    ; SINGLEELEM }
  | "UnionElem"     { Global.last "UnionElem"     ; UNIONELEM }
  | "IntrElem"      { Global.last "IntrElem"      ; INTRELEM }
  | "SetDiffElem"   { Global.last "SetDiffElem"   ; SETDIFFELEM }
  | "set2elem"      { Global.last "set2elem"      ; SET2ELEM }
  | "path2set"      { Global.last "path2set"      ; PATH2SET }
  | "addr2set"      { Global.last "addr2set"      ; ADDR2SET }
  | "orderlist"     { Global.last "orderlist"     ; ORDERLIST }
  | "skiplist"      { Global.last "skiplist"      ; SKIPLIST }
  | "getp"          { Global.last "getp"          ; GETP }
  | "append"        { Global.last "append"        ; APPEND } 
  | "reach"         { Global.last "reach"         ; REACH } 
  | "in"            { Global.last "in"            ; IN } 
  | "subseteq"      { Global.last "subseteq"      ; SUBSETEQ } 
  | "inTh"          { Global.last "inTh"          ; INTH } 
  | "subseteqTh"    { Global.last "subseteqTh"    ; SUBSETEQTH }
  | "inInt"         { Global.last "inInt"         ; ININT }
  | "subseteqInt"   { Global.last "subseteqInt"   ; SUBSETEQINT }
  | "inElem"        { Global.last "inElem"        ; INELEM }
  | "subseteqElem"  { Global.last "subseteqElem"  ; SUBSETEQELEM }
  | "setIntMin"     { Global.last "setIntMin"     ; SETINTMIN }
  | "setIntMax"     { Global.last "setIntMax"     ; SETINTMAX }
  | "Th"            { Global.last "Th"            ; THREAD }
  | '['             { Global.last "["             ; OPEN_BRACKET }
  | ']'             { Global.last "]"             ; CLOSE_BRACKET }
  | '('             { Global.last "("             ; OPEN_PAREN }
  | ')'             { Global.last ")"             ; CLOSE_PAREN }
  | '|'             { Global.last "|"             ; VERTICAL_BAR }
  | '='             { Global.last "="             ; EQUALS }
  | "!="            { Global.last "!="            ; NOT_EQUALS }
  | ":="            { Global.last ":="            ; ASSIGN }
  | "/\\"           { Global.last "/\\"           ; LOGICAL_AND }
  | "and"           { Global.last "and"           ; LOGICAL_AND }
  | "\\/"           { Global.last "\\/"           ; LOGICAL_OR  }
  | "or"            { Global.last "or"            ; LOGICAL_OR  }
  | "->"            { Global.last "->"            ; LOGICAL_THEN }
  | "<->"           { Global.last "<->"           ; LOGICAL_IFF }
  | '~'             { Global.last "~"             ; LOGICAL_NOT }
  | "true"          { Global.last "true"          ; LOGICAL_TRUE }
  | "false"         { Global.last "false"         ; LOGICAL_FALSE }
  | '{'             { Global.last "{"             ; OPEN_SET }
  | '}'             { Global.last "}"             ; CLOSE_SET }
  | '.'             { Global.last "."             ; DOT }
  | ','             { Global.last ","             ; COMMA }
  | ':'             { Global.last ":"             ; COLON }
  | "::"            { Global.last "::"            ; DOUBLECOLON }
  | ';'             { Global.last ";"             ; SEMICOLON }
  | '+'             { Global.last "+"             ; MATH_PLUS }
  | '-'             { Global.last "-"             ; MATH_MINUS }
  | '*'             { Global.last "*"             ; MATH_MULT }
  | '/'             { Global.last "/"             ; MATH_DIV }
  | '<'             { Global.last "<"             ; MATH_LESS }
  | '>'             { Global.last ">"             ; MATH_GREATER }
  | "<="            { Global.last "<="            ; MATH_LESS_EQ }
  | ">="            { Global.last ">="            ; MATH_GREATER_EQ }
  | '@'             { Global.last "@"             ; AT }
  | '_'             { Global.last "_"             ; UNDERSCORE }
  | '#'             { Global.last "#"             ; SHARP }
  | "->"            { Global.last "->"            ; EDGE_ARROW }
  | "=>"            { Global.last "=>"            ; LARGE_EDGE_ARROW }
  | "arrUpd"        { Global.last "arrUpd"        ; ARR_UPDATE }
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letter alphanum*) as id { Global.last id; IDENT (id,Global.get_linenum()) }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise LexerError
                      }
