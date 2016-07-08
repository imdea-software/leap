
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

open Z3ModelParser

exception LexerError

}

let whitespc = [' ' '\t']
let letter = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alphanum = ['A'-'Z' 'a'-'z' '0'-'9' '/' ''' '@' '_' '!' ':']
let alphanum_not_prime = ['A'-'Z' 'a'-'z' '0'-'9' '/' '@' ]
let almostany =['A'-'Z' 'a'-'z' '0'-'9' '_' ' ' '.' '/' '-' '(' ')' '\'' ',' '!' ':']

rule norm = parse
  | '='                          {Global.last "="              ; EQUAL                                }
  | '('                          {Global.last "("              ; OPEN_PAREN                           }
  | ')'                          {Global.last ")"              ; CLOSE_PAREN                          }
  | ";;"                         {Global.last ";;"             ; DOUBLE_SEMICOLON                     }
  | '_'                          {Global.last "_"              ; UNDERSCORE                           }
  | "model "                     {Global.last "model"          ; MODEL                                }
  | "declare-fun"                {Global.last "declare-fun"    ; DECLARE_FUN                          }
  | "define-fun"                 {Global.last "define-fun"     ; DEFINE_FUN                           }
  | "Array"                      {Global.last "Array"          ; ARRAY                                }
  | "as-array"                   {Global.last "as-array"       ; AS_ARRAY                             }
  | "as"                         {Global.last "as"             ; AS                                   }
  | "const"                      {Global.last "const"          ; CONST                                }
  | "store"                      {Global.last "store"          ; STORE                                }
  | "forall"                     {Global.last "forall"         ; FORALL                               }
  | "or"                         {Global.last "or"             ; OR                                   }
  | "and"                        {Global.last "and"            ; AND                                  }
  | "ite"                        {Global.last "ite"            ; ITE                                  }
  | ("tt_")(digit+ as id)        {Global.last ("tt_" ^ id)     ; TID_ELEM ("tt_" ^ id)                }
  | "NoThread"                   {Global.last "NoThread"       ; NO_THREAD                            }
  | ("aa_")(digit+ as id)        {Global.last ("aa_" ^ id)     ; ADDR_ELEM ("aa_" ^ id)               }
  | ("ee_")(digit+ as id)        {Global.last ("ee_" ^ id)     ; ELEM_ELEM ("ee_" ^ id)               }
  | "error"                      {Global.last "error"          ; ERROR                                }
  | "true"                       {Global.last "true"           ; BOOL (true)                          }
  | "false"                      {Global.last "false"          ; BOOL (false)                         }
  | "k!"(digit+ as id)           {Global.last ("k!" ^ id)      ; ARRAY_ID (int_of_string id)          }
  | (digit+) as num              {Global.last num              ; NUMBER (int_of_string num)           }
  | "(- "(digit+ as num)")"      {Global.last num              ; NUMBER (-(int_of_string num))        }
  | (letter alphanum*) as id     {Global.last id               ; IDENT (id,Global.get_linenum())      }
  | ("$" alphanum*) as id        {Global.last id               ; IDENT (id,Global.get_linenum())      }
  | whitespc                     {Global.last "whitespc"       ; norm lexbuf                          }
  | '\n'                         {Global.last "\\n"            ; Global.incr_linenum (); norm lexbuf  }
  | eof                          {Global.last "EOF"            ; EOF                                  }
  | _ as x                       {Global.last (String.make 1 x);
                                print_endline ("Bad token: " ^ (String.make 1 x)); raise LexerError }
