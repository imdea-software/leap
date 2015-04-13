{
open ExprParser

exception LexerError

let keyword_table = Hashtbl.create 128
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
          [ ("TidConstraint", TID_CONSTRAINT);
            ("Rho"          , RHO);
            ("Goal"         , GOAL);
            ("Tid"          , TRANSITION_TID);
            ("Line"         , LINE);
            ("Support"      , SUPPORT);
            ("Diagram"      , DIAGRAM);
            ("begin"        , BEGIN);
            ("end"          , END);
            ("Boxes"        , BOXES);
            ("Nodes"        , NODES);
            ("Initial"      , INITIAL);
            ("Edges"        , EDGES);
            ("Acceptance"   , ACCEPTANCE);
            ("invariant"    , INVARIANT);
            ("formula"      , FORMULA);
            ("vars"         , VARS);
            ("error"        , ERROR);
            ("mkcell"       , MKCELL);
            ("data"         , DATA);
            ("next"         , NEXT);
            ("nextat"       , NEXTAT);
            ("arr"          , ARR);
            ("tids"         , TIDS);
            ("max"          , MAX);
            ("firstlocked"  , FIRSTLOCKED);
            ("lastlocked"   , LASTLOCKED);
            ("lockset"      , LOCKSET);
            ("lockid"       , LOCKID);
            ("lock"         , LOCK);
            ("lockat"       , LOCKAT);
            ("unlock"       , UNLOCK);
            ("unlockat"     , UNLOCKAT);
            ("rd"           , MEMORY_READ);
            ("null"         , NULL);
            ("lowestElem"   , LOWEST_ELEM);
            ("highestElem"  , HIGHEST_ELEM);
            ("upd"          , UPDATE);
            ("epsilon"      , EPSILON);
            ("EmptySet"     , EMPTYSET);
            ("Union"        , UNION);
            ("Intr"         , INTR);
            ("SetDiff"      , SETDIFF );
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
            ("SetLower"     , SETLOWER);
            ("EmptySetElem" , EMPTYSETELEM);
            ("SingleElem"   , SINGLEELEM);
            ("UnionElem"    , UNIONELEM);
            ("IntrElem"     , INTRELEM);
            ("SetDiffElem"  , SETDIFFELEM);
            ("set2elem"     , SET2ELEM);
            ("path2set"     , PATH2SET);
            ("addr2set"     , ADDR2SET);
            ("orderlist"    , ORDERLIST);
            ("skiplist"     , SKIPLIST);
            ("getp"         , GETP);
            ("append"       , APPEND );
            ("reach"        , REACH );
            ("in"           , IN );
            ("subseteq"     , SUBSETEQ );
            ("inTh"         , INTH );
            ("subseteqTh"   , SUBSETEQTH);
            ("inInt"        , ININT);
            ("subseteqInt"  , SUBSETEQINT);
            ("inElem"       , INELEM);
            ("subseteqElem" , SUBSETEQELEM);
            ("setIntMin"    , SETINTMIN);
            ("setIntMax"    , SETINTMAX);
            ("spmin"        , SETPAIRMIN);
            ("spmax"        , SETPAIRMAX);
            ("int_of"       , INTOF);
            ("tid_of"       , TIDOF);
            ("spempty"      , SETPAIREMPTY);
            ("spsingle"     , SETPAIRSINGLE);
            ("spunion"      , SETPAIRUNION);
            ("spintr"       , SETPAIRINTR);
            ("spdiff"       , SETPAIRDIFF);
            ("splower"      , SETPAIRLOWER);
            ("spin"         , SETPAIRIN);
            ("spsubseteq"   , SETPAIRSUBSETEQ);
            ("intidpair"    , SETPAIRINTIDPAIR);
            ("inintpair"    , SETPAIRININTPAIR);
            ("uniquetid"    , SETPAIRUNIQUETID);
            ("uniqueint"    , SETPAIRUNIQUEINT);
            ("Th"           , THREAD);
            ("true"         , LOGICAL_TRUE);
            ("false"        , LOGICAL_FALSE);
            ("Good"         , GOOD);
            ("Bad"          , BAD);
            ("arrUpd"       , ARR_UPDATE);
            ("subset_op"    , WF_INTSUBSET);
            ("pairsubset_op", WF_PAIRSUBSET);
            ("addrsubset_op", WF_ADDRSUBSET);
            ("elemsubset_op", WF_ELEMSUBSET);
            ("tidsubset_op" , WF_TIDSUBSET);
            ("less_op"      , WF_INTLESS)]
}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let letterordollar = ['A'-'Z' 'a'-'z' '$']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '_' '/' ''' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',']

rule norm = parse
  | '['             { Global.last "["             ; OPEN_BRACKET }
  | ']'             { Global.last "]"             ; CLOSE_BRACKET }
  | '('             { Global.last "("             ; OPEN_PAREN }
  | ')'             { Global.last ")"             ; CLOSE_PAREN }
  | '|'             { Global.last "|"             ; VERTICAL_BAR }
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
  | "-->"           { Global.last "-->"           ; EDGE_ARROW }
  | "-{"            { Global.last "-{"            ; EDGE_ARROW_OPEN }
  | "}->"           { Global.last "}->"           ; EDGE_ARROW_CLOSE }
  | "<<"            { Global.last "<<"            ; OPEN_ANGLE }
  | ">>"            { Global.last ">>"            ; CLOSE_ANGLE }
  | (digit+) as num { Global.last num; NUMBER (int_of_string num) }
  | (letterordollar alphanum*) as id
          { Global.last id;
            try
              Hashtbl.find keyword_table id
            with Not_found -> 
              IDENT (id, Global.get_linenum())
          }
  | whitespc          { Global.last "whitespc"; norm lexbuf }
  | '\n'              { Global.last "\\n"; Global.incr_linenum (); norm lexbuf }
  | eof               { Global.last "EOF"; EOF }
  | _ as x            { Global.last (String.make 1 x);
                          print_endline ("Bad token: " ^ (String.make 1 x));
                          raise(LexerError)
                      }
