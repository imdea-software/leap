%{
open Printf

open LeapLib
open Global
open Hashtbl

module Expr = Expression
module NumExpr = NumExpression

let get_name id = fst id
let get_line id = snd id

%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token OPEN_PAREN CLOSE_PAREN
%token COLON EQUALS NOT_EQUALS
%token LOGICAL_AND LOGICAL_OR LOGICAL_NOT LOGICAL_THEN LOGICAL_IFF
%token LOGICAL_TRUE LOGICAL_FALSE

%token MATH_PLUS MATH_MINUS MATH_MULT MATH_DIV MATH_LESS MATH_GREATER
%token MATH_LESS_EQ MATH_GREATER_EQ

%token EOF

%nonassoc EQUALS NOT_EQUALS MATH_LESS MATH_GREATER MATH_LESS_EQ MATH_GREATER_EQ
%nonassoc IDENT

%right LOGICAL_AND
%right LOGICAL_OR
%right LOGICAL_THEN
%right LOGICAL_IFF
%nonassoc LOGICAL_NOT


%left MATH_PLUS MATH_MINUS
%left MATH_MULT MATH_DIV
%right MATH_NEG


%start invariant_list
%start specification


%type <(string * NumExpression.formula)> one_spec
%type <(string * NumExpression.formula) list> specification
%type <(string * (NumExpression.conjunctive_formula)) list> invariant_list
%type <(string * NumExpression.conjunctive_formula)> one_invariant

%type <NumExpression.formula> formula
%type <NumExpression.literal> literal
%type <NumExpression.conjunctive_formula> conjunction_of_literals
%type <NumExpression.literal list> literal_list
%type <NumExpression.integer> integer
%type <NumExpression.term> term


%%
specification :
one_spec 
{ [$1] }
| one_spec specification
{ $1::$2 }

one_spec :
IDENT COLON formula
{ (get_name $1,$3) }

invariant_list:
|  one_invariant
  {  [ $1 ] }
| one_invariant invariant_list
  {  $1::$2 }

one_invariant:
  | IDENT COLON conjunction_of_literals
   {   (get_name $1,$3) }

formula :
  | OPEN_PAREN formula CLOSE_PAREN
      { $2 }
  | literal
      { NumExpr.Literal $1 }
  | LOGICAL_TRUE
      { NumExpr.True }
  | LOGICAL_FALSE
      { NumExpr.False }
  | LOGICAL_NOT formula
      { NumExpr.Not $2 }
  | formula LOGICAL_AND formula
      { NumExpr.And ($1, $3) }
  | formula LOGICAL_OR formula
      { NumExpr.Or ($1, $3) }
  | formula LOGICAL_THEN formula
      { NumExpr.Implies ($1, $3) }
  | formula LOGICAL_IFF formula
      { NumExpr.Iff ($1, $3) }


conjunction_of_literals : 
  | LOGICAL_FALSE
      { NumExpr.ConjFalse }
  | LOGICAL_TRUE
      { NumExpr.ConjTrue }
  |  literal_list
      { NumExpr.Conjuncts $1 }

literal_list :
  | literal
      { [$1] }
  | literal LOGICAL_AND literal_list
      { $1::$3 }

literal :
   integer MATH_LESS integer
    {
      NumExpr.Atom (NumExpr.Less ($1, $3))
    }
  | integer MATH_GREATER integer
    {
      NumExpr.Atom (NumExpr.Greater ($1, $3))
    }
  | integer MATH_LESS_EQ integer
    {
      NumExpr.Atom (NumExpr.LessEq ($1, $3))
    }
  | integer MATH_GREATER_EQ integer
    {
      NumExpr.Atom (NumExpr.GreaterEq ($1, $3))
    }
  | term EQUALS term
    {
      NumExpr.Atom (NumExpr.Eq($1,$3))
    }
  | term NOT_EQUALS term
    {
      NumExpr.Atom (NumExpr.InEq($1,$3))
    }


term :
  | integer
    { NumExpr.IntV $1 }
/* Remains the support for sets, if necessary */


integer :
  | IDENT
      {
        let v = NumExpr.build_var (get_name $1) NumExpr.Int false None None
        in
          NumExpr.Var v
      }
  | OPEN_PAREN integer CLOSE_PAREN
    { $2 }
  | NUMBER
    { NumExpr.Val $1 }
  | MATH_MINUS integer %prec MATH_NEG
    {
      NumExpr.Neg $2
    }
  | integer MATH_PLUS integer
    {
      NumExpr.Add ($1,$3)
    }
  | integer MATH_MINUS integer
    {
      NumExpr.Sub ($1,$3)
    }
  | integer MATH_MULT integer
    {
      NumExpr.Mul ($1,$3)
    }
  | integer MATH_DIV integer
    {
      NumExpr.Div ($1,$3)
    }


