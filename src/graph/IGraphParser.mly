%{

(* Type rename *)

type case_t = Expression.pc_t         *
              Premise.t list          *
              Tag.f_tag list          *
              Tactics.proof_plan

(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id



%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token SEQ_ARROW CONC_ARROW BOX COMMA COLON DOUBLECOLON SEMICOLON
%token OPEN_BRACK CLOSE_BRACK OPEN_BRACE CLOSE_BRACE OPEN_PAREN CLOSE_PAREN
%token BAR
%token SELF_PREMISE OTHERS_PREMISE
%token SMP_UNION SMP_PRUNING SMP_DNF
%token TACTICS FACTS
%token EOF


%start graph
%start pvd_support

%type <PVD.support_t> pvd_support
%type <(PVD.supp_line_t * Tactics.proof_plan)> tactic_case
%type <(PVD.supp_line_t * Tactics.proof_plan) list> tactic_case_list
%type <(PVD.supp_line_t * Tag.f_tag list)> fact
%type <(PVD.supp_line_t * Tag.f_tag list) list> fact_list

%type <IGraph.t> graph
%type <IGraph.rule_t list> rule_list
%type <IGraph.rule_t> rule
%type <Tag.f_tag list> maybe_empty_inv_list
%type <Tag.f_tag list> inv_list
%type <Tag.f_tag> inv
%type <Tag.f_tag list> inv_group
%type <string list> ident_list
%type <case_t list> cases
%type <case_t list> seq_cases
%type <case_t list> case_list
%type <case_t list> seq_case_list
%type <case_t> case
%type <case_t> seq_case
%type <Premise.t list> premise
%type <Tactics.proof_plan> tactics
%type <(Smp.cutoff_strategy_t option)> smp_strategy
%type <(Tactics.support_split_tactic_t)> support_split_tactic
%type <(Tactics.support_tactic_t)> support_tactic
%type <(Tactics.formula_split_tactic_t)> formula_split_tactic
%type <(Tactics.formula_tactic_t)> formula_tactic
%type <(Tactics.support_split_tactic_t list)> support_split_tactic_list
%type <(Tactics.support_tactic_t list)> support_tactic_list
%type <(Tactics.formula_split_tactic_t list)> formula_split_tactic_list
%type <(Tactics.formula_tactic_t list)> formula_tactic_list



%%

/* PVD SUPPORT */

pvd_support :
  | TACTICS COLON tactic_case_list
    FACTS COLON fact_list
    {
      let tactics = $3 in
      let facts = $6 in
      PVD.new_support tactics facts
    }


tactic_case_list :
  |
    { [] }
  | tactic_case tactic_case_list
    { $1 :: $2 }


tactic_case :
  | tactics SEMICOLON
    { (PVD.All, $1) }
  | NUMBER COLON tactics SEMICOLON
    { (PVD.Trans $1, $3) }


fact_list :
  |
    { [] }
  | fact fact_list
    { $1 :: $2 }


fact :
  | inv_list SEMICOLON
    { (PVD.All, $1) }
  | NUMBER COLON inv_list SEMICOLON
    { (PVD.Trans $1, $3) }


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
  | inv_group
    { $1 }
  | inv
    { [$1] }
  | inv_group COMMA inv_list
    { $1 @ $3 }
  | inv COMMA inv_list
    {
      let i = $1 in
      let is = $3
      in
        i :: is
    }


inv_group :
  | IDENT DOUBLECOLON OPEN_BRACE ident_list CLOSE_BRACE
    { List.map (fun st -> Tag.new_tag (get_name $1) st) $4 }


ident_list :
  | IDENT
    { [(get_name $1)] }
  | IDENT COMMA ident_list
    { (get_name $1) :: $3 }


inv :
  | IDENT
    { Tag.new_tag (get_name $1) "" }
  | IDENT DOUBLECOLON IDENT
    {
      Tag.new_tag (get_name $1) (get_name $3)
    }


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
        (pc, [Premise.SelfConseq], phi_list, tacs)
    }


premise :
  |
    { [Premise.SelfConseq; Premise.OthersConseq] }
  | SELF_PREMISE COLON
    { [Premise.SelfConseq] }
  | OTHERS_PREMISE COLON
    { [Premise.OthersConseq] }


tactics :
  |
    { Tactics.new_proof_plan None [] [] [] [] }
  | OPEN_BRACE smp_strategy
               support_split_tactic_list
               support_tactic_list
               formula_split_tactic_list
               formula_tactic_list CLOSE_BRACE
    {
      Tactics.new_proof_plan $2 $3 $4 $5 $6
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


support_tactic_list :
  | BAR
    { [] }
  | support_tactic support_tactic_list
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
  | IDENT
    { Tactics.support_split_tactic_from_string (get_name $1) }


support_tactic :
  | IDENT
    { Tactics.support_tactic_from_string (get_name $1) }


formula_split_tactic :
  | IDENT
    { Tactics.formula_split_tactic_from_string (get_name $1) }


formula_tactic :
  | IDENT
    { Tactics.formula_tactic_from_string (get_name $1) }
