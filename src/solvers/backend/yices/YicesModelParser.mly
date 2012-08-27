%{
open Printf

open Global
open LeapLib

(* Type rename *)

module GM = GenericModel


exception Not_implemented of string

(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id


(* Mappings *)
let model = GM.new_model ()


(* ID counter *)
let id_count : int ref = ref 0



(* Updates and propagates a cell id update *)
let gen_fresh_id (unit) : int =
  let _ = incr id_count
  in
    !id_count


%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token <string> TID_ELEM
%token <string> ADDR_ELEM
%token <string> ELEM_ELEM
%token <bool> BOOL

%token EQUAL OPEN_PAREN CLOSE_PAREN DOUBLE_COLON SELECT MK_RECORD
%token NO_THREAD ERROR NULL
%token EOF


%start generic_model


%type <GenericModel.t> generic_model

%type <unit> assertion_list
%type <unit> assertion
%type <unit> sel
%type <GM.var> var
%type <GM.id> fun_name
%type <(GM.id option) list> param_list
%type <GM.value> value
%type <GM.vals> constant
%type <GM.id * (GM.id * GM.vals) list> record
%type <(GM.id * GM.vals) list> field_list
%type <GM.id * GM.vals> field


%%


/* MODEL FOR COUNTER EXAMPLE PARSER */

generic_model :
  | assertion_list
    { let m = GM.copy_model model in
      let _ = GM.clear_model model
      in
        m
    }


assertion_list :
  | assertion
    { () }
  | assertion assertion_list
    { () }


assertion :
  | OPEN_PAREN EQUAL var var CLOSE_PAREN
    {
      GM.unify model $3 $4
    }
  | OPEN_PAREN EQUAL var value CLOSE_PAREN
    {
      match $3 with
      | GM.Var v               -> GM.decl_const model v $4
      | GM.Function (f,params) -> GM.decl_fun model f params $4
    }
  | OPEN_PAREN EQUAL value var CLOSE_PAREN
    {
      match $4 with
      | GM.Var v               -> GM.decl_const model v $3
      | GM.Function (f,params) -> GM.decl_fun model f params $3
    }
  | OPEN_PAREN EQUAL OPEN_PAREN SELECT sel IDENT CLOSE_PAREN value CLOSE_PAREN
    { () }


sel :
  | var
    { () }
  | record
    { () }


var :
  | ERROR
    { GM.Var "error" }
  | IDENT
    { GM.Var (get_name $1) }
  | OPEN_PAREN fun_name param_list CLOSE_PAREN
    { GM.Function ($2, $3) }


fun_name :
  | IDENT
    { get_name $1 }
  | constant
    { $1 }


param_list :
  | constant
    { [Some $1] }
  | constant param_list
    { Some $1 :: $2 }


value :
  | constant
    { GM.Single $1 }
  | record
    { GM.Record $1 }


constant :
  | BOOL
    { if $1 then "true" else "false" }
  | TID_ELEM
    { $1 }
  | ADDR_ELEM
    { $1 }
  | ELEM_ELEM
    { $1 }
  | NUMBER
    { (string_of_int $1) }
  | NO_THREAD
    { "NoThread" }
  | NULL
    { "null" }



record :
  | OPEN_PAREN MK_RECORD field_list CLOSE_PAREN
    { ("mk-record", $3) }


field_list :
  | field
    { [$1] }
  | field field_list
    { $1 :: $2 }


field :
  | IDENT DOUBLE_COLON constant
    { (get_name $1, $3) }
