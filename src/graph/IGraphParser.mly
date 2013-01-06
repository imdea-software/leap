%{
open Printf

open LeapLib
open Global

(* Type rename *)

type graph_t = IGraph.iGraph_t

type case_t = Expression.pc_t         *
              IGraph.premise_t list   *
              Tag.f_tag list          *
              Tactics.t

(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id



%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token SEQ_ARROW CONC_ARROW COMMA COLON SEMICOLON
%token OPEN_BRACK CLOSE_BRACK OPEN_BRACE CLOSE_BRACE OPEN_PAREN CLOSE_PAREN
%token BAR
%token NORMAL_PREMISE EXTRA_PREMISE
%token SMP_UNION SMP_PRUNING SMP_DNF
%token REDUCE_TACTIC REDUCE2_TACTIC SPLIT_TACTIC SIMPL_TACTIC
%token SOLVE_TACT_CASES
%token EOF


%start graph


%type <IGraph.iGraph_t> graph
%type <IGraph.rule_t list> rule_list
%type <IGraph.rule_t> rule
%type <Tag.f_tag list> maybe_empty_inv_list
%type <Tag.f_tag list> inv_list
%type <Tag.f_tag> inv
%type <case_t list> cases
%type <case_t list> case_list
%type <case_t> case
%type <IGraph.premise_t list> premise
%type <Tactics.t> tactics
%type <(Tactics.smp_tactic_t option * Tactics.solve_tactic_t option)> smp_tactic
%type <Tactics.solve_tactic_t option> solve_tactic
%type <Tactics.pre_tac_t list> pre_tactic_list
%type <Tactics.pre_tac_t> pre_tactic
%type <Tactics.post_tac_t list> post_tactic_list
%type <Tactics.post_tac_t> post_tactic


%%


/* GRAPH PARSER */

graph :
  |
    { IGraph.empty_igraph() }
  | rule_list
    { IGraph.new_igraph($1) }


rule_list :
  | rule
    { [$1] }
  | rule rule_list
    {
      let r = $1 in
      let rs = $2
      in
        r :: rs
    }


rule :
  | CONC_ARROW inv cases tactics
    {
      let i = $2 in
      let cs = $3 in
      let ts = $4 in
      let _ = Printf.printf "tactics size: %i\n" (List.length (Tactics.post_tacs ts))
      in
        IGraph.new_rule [] i cs ts
    }
  | inv_list CONC_ARROW inv cases tactics
    {
      let sup = $1 in
      let i = $3 in
      let cs = $4 in
      let ts = $5 in
      let _ = Printf.printf "tactics size: %i\n" (List.length (Tactics.post_tacs ts))
      in
        IGraph.new_rule sup i cs ts
    }


maybe_empty_inv_list :
  |
    { [] }
  | inv_list
    { $1 }


inv_list :
  | inv
    { [$1] }
  | inv COMMA inv_list
    {
      let i = $1 in
      let is = $3
      in
        i :: is
    }

inv :
  | IDENT
    { Tag.new_tag (get_name $1) }


cases :
  |
    { [] }
  | OPEN_BRACK case_list CLOSE_BRACK
    { $2 }


case_list :
  | case
    { [$1] }
  | case SEMICOLON case_list
    {
      let c = $1 in
      let cs = $3
      in
        c :: cs
    }


case :
  | NUMBER COLON premise maybe_empty_inv_list tactics
    {
      let pc = $1 in
      let prem = $3 in
      let phi_list = $4 in
      let tacs = $5
      in
        (pc, prem, phi_list, tacs)
    }

premise :
  |
    { [IGraph.Normal; IGraph.Extra] }
  | NORMAL_PREMISE COLON
    { [IGraph.Normal] }
  | EXTRA_PREMISE COLON
    { [IGraph.Extra] }


tactics :
  |
    { Tactics.new_tactics None None [] [] }
  | OPEN_BRACE smp_tactic pre_tactic_list BAR
      post_tactic_list CLOSE_BRACE
    {
      let (smp,solve_tact) = $2 in
      let pre = $3 in
      let post = $5
      in
        Tactics.new_tactics smp solve_tact pre post
    }


pre_tactic_list :
  |
    { [] }
  | pre_tactic pre_tactic_list
    { $1 :: $2 }


post_tactic_list :
  |
    { [] }
  | post_tactic post_tactic_list
    { $1 :: $2 }


smp_tactic :
  |
    { (None, None) }
  | SMP_UNION solve_tactic COLON
    { (Some Tactics.Union, $2) }
  | SMP_PRUNING solve_tactic COLON
    { (Some Tactics.Pruning, $2) }
  | SMP_DNF solve_tactic COLON
    { (Some Tactics.Dnf, $2) }


solve_tactic :
  |
    { None }
  | OPEN_PAREN SOLVE_TACT_CASES CLOSE_PAREN
    { Some Tactics.Cases }


pre_tactic :
  | REDUCE_TACTIC
    { Tactics.Reduce }
  | REDUCE2_TACTIC
    { Tactics.Reduce2 }


post_tactic :
  | SPLIT_TACTIC
    { Tactics.SplitConseq }
  | SIMPL_TACTIC
    { Tactics.SimplPCVoc }
