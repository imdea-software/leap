%{
open Printf

open LeapLib
open Global

(* Type rename *)

type graph_t = IGraph.iGraph_t

type case_t = Expression.pc_t         *
              IGraph.premise_t list   *
              Tag.f_tag list          *
              Tactics.proof_plan

(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id



%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token SEQ_ARROW CONC_ARROW BOX COMMA COLON SEMICOLON
%token OPEN_BRACK CLOSE_BRACK OPEN_BRACE CLOSE_BRACE OPEN_PAREN CLOSE_PAREN
%token BAR
%token SELF_PREMISE OTHERS_PREMISE
%token SMP_UNION SMP_PRUNING SMP_DNF
%token SUPP_SPLIT_GOAL_TACTIC
%token SUPP_FULL_TACTIC SUPP_REDUCE_TACTIC SUPP_REDUCE2_TACTIC
%token FORMULA_SPLIT_CONSEQUENT_TACTIC
%token FORMULA_SIMPLIFYPC_TACTIC FORMULA_PROPAGATE_TACTIC FORMULA_FILTER_TACTIC
%token EOF


%start graph


%type <IGraph.iGraph_t> graph
%type <IGraph.rule_t list> rule_list
%type <IGraph.rule_t> rule
%type <Tag.f_tag list> maybe_empty_inv_list
%type <Tag.f_tag list> inv_list
%type <Tag.f_tag> inv
%type <case_t list> cases
%type <case_t list> seq_cases
%type <case_t list> case_list
%type <case_t list> seq_case_list
%type <case_t> case
%type <case_t> seq_case
%type <IGraph.premise_t list> premise
%type <Tactics.proof_plan> tactics
%type <(Smp.cutoff_strategy_t option)> smp_strategy
%type <(Tactics.support_split_tactic)> support_split_tactic
%type <(Tactics.support_tactic)> support_tactic
%type <(Tactics.formula_split_tactic)> formula_split_tactic
%type <(Tactics.formula_tactic)> formula_tactic
%type <(Tactics.support_split_tactic list)> support_split_tactic_list
%type <(Tactics.formula_split_tactic list)> formula_split_tactic_list
%type <(Tactics.formula_tactic list)> formula_tactic_list



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
  | maybe_empty_inv_list CONC_ARROW inv cases tactics
    {
      let sup = $1 in
      let i = $3 in
      let cs = $4 in
      let ts = $5 in
(*        LOG "Concurrent tactics size: %i" (List.length (Tactics.post_tacs ts)) LEVEL DEBUG; *)
        IGraph.new_rule IGraph.Concurrent sup i cs ts
    }
  | maybe_empty_inv_list SEQ_ARROW inv seq_cases tactics
    {
      let sup = $1 in
      let i = $3 in
      let cs = $4 in
      let ts = $5 in
(*        LOG "Sequential tactics size: %i" (List.length (Tactics.post_tacs ts)) LEVEL DEBUG; *)
        IGraph.new_rule IGraph.Sequential sup i cs ts
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


seq_cases :
  |
    { [] }
  | OPEN_BRACK seq_case_list CLOSE_BRACK
    { $2 }


case_list :
  | case
    { [$1] }
  | case SEMICOLON case_list
    { $1 :: $3 }


seq_case_list :
  | seq_case
    { [$1] }
  | seq_case SEMICOLON seq_case_list
    { $1 :: $3 }


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


seq_case :
  | NUMBER COLON maybe_empty_inv_list tactics
    {
      let pc = $1 in
      let phi_list = $3 in
      let tacs = $4
      in
        (pc, [IGraph.SelfConseq], phi_list, tacs)
    }


premise :
  |
    { [IGraph.SelfConseq; IGraph.OthersConseq] }
  | SELF_PREMISE COLON
    { [IGraph.SelfConseq] }
  | OTHERS_PREMISE COLON
    { [IGraph.OthersConseq] }


tactics :
  |
    { Tactics.new_proof_plan None [] [] [] [] }
  | OPEN_BRACE smp_strategy
               support_split_tactic_list
               support_tactic
               formula_split_tactic_list
               formula_tactic_list CLOSE_BRACE
    {
      Tactics.new_proof_plan $2 (List.map Tactics.pick_support_split_tac $3) [$4]
                                (List.map Tactics.pick_formula_split_tac $5) $6
    }


smp_strategy :
  |
    { None }
  | SMP_UNION COLON
    { Some Smp.Union }
  | SMP_PRUNING COLON
    { Some Smp.Pruning }
  | SMP_DNF COLON
    { Some Smp.Dnf }


support_split_tactic_list :
  | BAR
    { [] }
  | support_split_tactic support_split_tactic_list
    { $1 :: $2 }


formula_split_tactic_list :
  | BAR
    { [] }
  | formula_split_tactic formula_split_tactic_list
    { $1 :: $2 }


formula_tactic_list :
  |
    { [] }
  | formula_tactic formula_tactic_list
    { $1 :: $2 }


support_split_tactic :
  | SUPP_SPLIT_GOAL_TACTIC
    { Tactics.SplitGoal }


support_tactic :
  | SUPP_FULL_TACTIC BAR
    { Tactics.Full }
  | SUPP_REDUCE_TACTIC BAR
    { Tactics.Reduce }
  | SUPP_REDUCE2_TACTIC BAR
    { Tactics.Reduce2 }


formula_split_tactic :
  | FORMULA_SPLIT_CONSEQUENT_TACTIC
    { Tactics.SplitConsequent }


formula_tactic :
  | FORMULA_SIMPLIFYPC_TACTIC
    { Tactics.SimplifyPC }
  | FORMULA_PROPAGATE_TACTIC
    { Tactics.PropositionalPropagate }
  | FORMULA_FILTER_TACTIC
    { Tactics.FilterStrict }
