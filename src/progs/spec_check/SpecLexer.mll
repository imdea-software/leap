
{

(***********************************************************************)
(*                                                                     *)
(*                                 LEAP                                *)
(*                                                                     *)
(*               Alejandro Sanchez, IMDEA Software Institute           *)
(*                                                                     *)
(*                                                                     *)
(*      Copyright 2011 IMDEA Software Institute                        *)
(*                                                                     *)
(*  Licensed under the Apache License, Version 2.0 (the "License");    *)
(*  you may not use this file except in compliance with the License.   *)
(*  You may obtain a copy of the License at                            *)
(*                                                                     *)
(*      http://www.apache.org/licenses/LICENSE-2.0                     *)
(*                                                                     *)
(*  Unless required by applicable law or agreed to in writing,         *)
(*  software distributed under the License is distributed on an        *)
(*  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,       *)
(*  either express or implied.                                         *)
(*  See the License for the specific language governing permissions    *)
(*  and limitations under the License.                                 *)
(*                                                                     *)
(***********************************************************************)

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
