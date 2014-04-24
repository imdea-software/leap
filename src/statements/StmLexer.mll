{
open Global
open StmParser

exception LexerError


let keyword_table = Hashtbl.create 40
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    [ "EmptySet",      EMPTYSET;
      "Union",         UNION;
      "Intr",          INTR;
      "SetDiff",       SETDIFF;
      "EmptySetTh",    EMPTYSETTH;
      "SingleTh",      SINGLETH;
      "UnionTh",       UNIONTH;
      "IntrTh",        INTRTH;
      "SetDiffTh",     SETDIFFTH;
      "EmptySetInt",   EMPTYSETINT;
      "SingleInt",     SINGLEINT;
      "UnionInt",      UNIONINT;
      "IntrInt",       INTRINT;
      "SetDiffInt",    SETDIFFINT;
      "EmptySetElem",  EMPTYSETELEM;
      "SingleElem",    SINGLEELEM;
      "UnionElem",     UNIONELEM;
      "IntrElem",      INTRELEM;
      "SetDiffElem",   SETDIFFELEM;
      "EmptySetPair",  EMPTYSETPAIR;
      "SinglePair",    SINGLEPAIR;
      "UnionPair",     UNIONPAIR;
      "IntrPair",      INTRPAIR;
      "SetDiffPair",   SETDIFFPAIR;
      "setPairMinInt", SETPAIRMININT;
      "setPairMinTid", SETPAIRMININT]

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '_' '/' ''' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']


rule norm = parse
  | "global"        { Global.last "global"        ; GLOBAL }
  | "ghost"         { Global.last "ghost"         ; GHOST }
  | "assume"        { Global.last "assume"        ; ASSUME }
  | "procedure"     { Global.last "procedure"     ; PROCEDURE }
  | "begin"         { Global.last "begin"         ; BEGIN }
  | "end"           { Global.last "end"           ; END }
  | "call"          { Global.last "call"          ; CALL }
  | "return"        { Global.last "return"        ; RETURN }
  | "skip"          { Global.last "skip"          ; ST_SKIP }
  | "assert"        { Global.last "assert"        ; ST_ASSERT }
  | "await"         { Global.last "await"         ; ST_AWAIT }
  | "noncritical"   { Global.last "noncritical"   ; ST_NONCRITICAL }
  | "critical"      { Global.last "critical"      ; ST_CRITICAL }
  | "if"            { Global.last "if"            ; ST_IF }
  | "then"          { Global.last "then"          ; ST_THEN }
  | "else"          { Global.last "else"          ; ST_ELSE }
  | "endif"         { Global.last "endif"         ; ST_ENDIF }
  | "while"         { Global.last "while"         ; ST_WHILE }
  | "do"            { Global.last "do"            ; ST_DO }
  | "endwhile"      { Global.last "endwhile"      ; ST_ENDWHILE }
  | "choice"        { Global.last "choice"        ; ST_CHOICE }
  | "_or_"          { Global.last "_or_"          ; ST_OR }
  | "endchoice"     { Global.last "endchoice"     ; ST_ENDCHOICE }
  | "malloc"        { Global.last "malloc"        ; MALLOC }
  | "mallocSL"      { Global.last "mallocSL"      ; MALLOCSL }
  | "mallocSLK"     { Global.last "mallocSLK"     ; MALLOCSLK }
  | "->"            { Global.last "-"             ; POINTER }
  | "error"         { Global.last "error"         ; ERROR }
  | "mkcell"        { Global.last "mkcell"        ; MKCELL }
  | "data"          { Global.last "data"          ; DATA }
  | "next"          { Global.last "next"          ; NEXT }
  | "nextat"        { Global.last "nextat"        ; NEXTAT }
  | "arr"           { Global.last "arr"           ; ARR }
  | "firstlocked"   { Global.last "fistlocked"    ; FIRSTLOCKED }
  | "lockid"        { Global.last "lockid"        ; LOCKID }
  | "lock"          { Global.last "lock"          ; LOCK }
  | "unlock"        { Global.last "unlock"        ; UNLOCK }
  | "rd"            { Global.last "rd"            ; MEMORY_READ }
  | "null"          { Global.last "null"          ; NULL }
  | "havocListElem" { Global.last "havocListElem" ; HAVOCLISTELEM }
  | "lowestElem"    { Global.last "lowestElem"    ; LOWEST_ELEM }
  | "highestElem"   { Global.last "highestElem"   ; HIGHEST_ELEM }
  | "havocSLElem"   { Global.last "havocSLElem"   ; HAVOCSKIPLISTELEM }
  | "havocLevel"    { Global.last "havocLevel"    ; HAVOCLEVEL }
  | "skiplist"      { Global.last "skiplist"      ; SKIPLIST }
  | "upd"           { Global.last "upd"           ; UPDATE }
  | "epsilon"       { Global.last "epsilon"       ; EPSILON }
  | "singlePath"    { Global.last "singlePath"    ; SINGLE_PATH }
  | "set2elem"      { Global.last "set2elem"      ; SET2ELEM }
  | "path2set"      { Global.last "path2set"      ; PATH2SET }
  | "addr2set"      { Global.last "addr2set"      ; ADDR2SET }
  | "orderlist"     { Global.last "orderlist"     ; ORDERLIST }
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
  | "inPair"        { Global.last "inPair"        ; INPAIR }
  | "subseteqPair"  { Global.last "subseteqPair"  ; SUBSETEQPAIR }
  | "setIntMin"     { Global.last "setIntMin"     ; SETINTMIN }
  | "setIntMax"     { Global.last "setIntMax"     ; SETINTMAX }
  | "Th"            { Global.last "Th"            ; THREAD }
  | "me"            { Global.last "me"            ; ME }
  | '['             { Global.last "["             ; OPEN_BRACKET }
  | ']'             { Global.last "]"             ; CLOSE_BRACKET }
  | '('             { Global.last "("             ; OPEN_PAREN }
  | ')'             { Global.last ")"             ; CLOSE_PAREN }
  | '|'             { Global.last "|"             ; VERTICAL_BAR }
  | '$'             { Global.last "$"             ; GHOST_DELIMITER }
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
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letter alphanum*) as id { Global.last id;
                               try
                                 Hashtbl.find keyword_table id
                               with Not_found ->
                                 IDENT (id,Global.get_linenum()) }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | "\r\n"            { Global.last "\\r\\n"; Global.incr_linenum (); norm lexbuf }
  | "\r"              { Global.last "\\r"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise LexerError
                      }
