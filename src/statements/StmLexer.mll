{
open Global
open StmParser

exception LexerError


let keyword_table = Hashtbl.create 128
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
          [ ("global"       , GLOBAL);
            ("ghost"        , GHOST);
            ("assume"       , ASSUME);
            ("procedure"    , PROCEDURE);
            ("begin"        , BEGIN);
            ("end"          , END);
            ("call"         , CALL);
            ("return"       , RETURN);
            ("skip"         , ST_SKIP);
            ("assert"       , ST_ASSERT);
            ("await"        , ST_AWAIT);
            ("noncritical"  , ST_NONCRITICAL);
            ("critical"     , ST_CRITICAL);
            ("if"           , ST_IF);
            ("then"         , ST_THEN);
            ("else"         , ST_ELSE);
            ("endif"        , ST_ENDIF);
            ("while"        , ST_WHILE);
            ("do"           , ST_DO);
            ("endwhile"     , ST_ENDWHILE);
            ("choice"       , ST_CHOICE);
            ("endchoice"    , ST_ENDCHOICE);
            ("malloc"       , MALLOC);
            ("mallocSL"     , MALLOCSL);
            ("mallocSLK"    , MALLOCSLK);
            ("error"        , ERROR);
            ("mkcell"       , MKCELL);
            ("data"         , DATA);
            ("next"         , NEXT);
            ("nextat"       , NEXTAT);
            ("arr"          , ARR);
            ("firstlocked"  , FIRSTLOCKED);
            ("lockid"       , LOCKID);
            ("lock"         , LOCK);
            ("unlock"       , UNLOCK);
            ("rd"           , MEMORY_READ);
            ("null"         , NULL);
            ("havocListElem", HAVOCLISTELEM);
            ("lowestElem"   , LOWEST_ELEM);
            ("highestElem"  , HIGHEST_ELEM);
            ("havocSLElem"  , HAVOCSKIPLISTELEM);
            ("havocLevel"   , HAVOCLEVEL);
            ("skiplist"     , SKIPLIST);
            ("upd"          , UPDATE);
            ("epsilon"      , EPSILON);
            ("singlePath"   , SINGLE_PATH);
            ("EmptySet"     , EMPTYSET);
            ("Union"        , UNION);
            ("Intr"         , INTR);
            ("SetDiff"      , SETDIFF);
            ("EmptySetTh"   , EMPTYSETTH);
            ("SingleTh"     , SINGLETH);
            ("UnionTh"      , UNIONTH);
            ("IntrTh"       , INTRTH);
            ("SetDiffTh"    , SETDIFFTH);
            ("EmptySetInt"  , EMPTYSETINT);
            ("SingleInt"    , SINGLEINT);
            ("UnionInt"     , UNIONINT);
            ("IntrInt"      , INTRINT);
            ("SetDiffInt"   , SETDIFFINT);
            ("EmptySetElem" , EMPTYSETELEM);
            ("SingleElem"   , SINGLEELEM);
            ("UnionElem"    , UNIONELEM);
            ("IntrElem"     , INTRELEM);
            ("SetDiffElem"  , SETDIFFELEM);
            ("set2elem"     , SET2ELEM);
            ("path2set"     , PATH2SET);
            ("addr2set"     , ADDR2SET);
            ("orderlist"    , ORDERLIST);
            ("getp"         , GETP);
            ("append"       , APPEND);
            ("reach"        , REACH);
            ("in"           , IN);
            ("subseteq"     , SUBSETEQ);
            ("inTh"         , INTH);
            ("subseteqTh"   , SUBSETEQTH);
            ("inInt"        , ININT);
            ("subseteqInt"  , SUBSETEQINT);
            ("inElem"       , INELEM);
            ("subseteqElem" , SUBSETEQELEM);
            ("setIntMin"    , SETINTMIN);
            ("setIntMax"    , SETINTMAX);
            ("psmin"        , SETPAIRMIN);
            ("psmax"        , SETPAIRMAX);
            ("tid_of"       , INTOF);
            ("int_of"       , TIDOF);
            ("spempty"      , SETPAIREMPTY);
            ("spsingle"     , SETPAIRSINGLE);
            ("spunion"      , SETPAIRUNION);
            ("spintr"       , SETPAIRINTR);
            ("spdiff"       , SETPAIRDIFF);
            ("spin"         , SETPAIRIN);
            ("spsubseteq"   , SETPAIRSUBSETEQ);
            ("Th"           , THREAD);
            ("me"           , ME);
            ("and"          , LOGICAL_AND);
            ("or"           , LOGICAL_OR );
            ("true"         , LOGICAL_TRUE);
            ("false"        , LOGICAL_FALSE)]
}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '_' '/' ''' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | "_or_"          { Global.last "_or_"          ; ST_OR }
  | "->"            { Global.last "-"             ; POINTER }
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
  | "\\/"           { Global.last "\\/"           ; LOGICAL_OR  }
  | "->"            { Global.last "->"            ; LOGICAL_THEN }
  | "<->"           { Global.last "<->"           ; LOGICAL_IFF }
  | '~'             { Global.last "~"             ; LOGICAL_NOT }
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
  | (letter alphanum*) as id
          { Global.last id;
            try
              Hashtbl.find keyword_table id
            with Not_found -> 
              IDENT (id, Global.get_linenum())
          }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | "\r\n"            { Global.last "\\r\\n"; Global.incr_linenum (); norm lexbuf }
  | "\r"              { Global.last "\\r"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise LexerError
                      }
