%{
open Printf

open LeapLib
open Global

module Expr   = Expression
module Vd     = Diagrams
module Symtbl = Exprsymtable

(* This code should be changed in the future *)
module Pos  = (val PosSolver.choose  "default"   : PosSolver.S)
module Tll  = (val TllSolver.choose  "default"   : TllSolver.S)
module Tslk = (val TslkSolver.choose "default" 1 : TslkSolver.S)
module Num  = (val NumSolver.choose  "default"   : NumSolver.S)
module VCG = VCGen.Make(Pos)(Tll)(Tslk)(Num)
module VD = Diagrams.Make(VCG)
(* This code should be changed in the future *)

type cond_op_t =
  | Less
  | Greater
  | LessEq
  | GreaterEq
  | In
  | SubsetEq
  | InTh
  | SubsetEqTh
  | InInt
  | SubsetEqInt
  | InElem
  | SubsetEqElem


exception WrongType of Expr.term
exception Sort_mismatch of Expr.varId * Expr.sort * Expr.sort
exception Not_sort_name of string
exception Duplicated_local_var of Expr.varId * Expr.sort
exception No_main
exception Unknown_procedure of string
exception Variable_not_in_procedure of Expr.varId * string
exception Wrong_assignment of Expr.term
exception Atomic_double_assignment of Expr.expr_t
exception Unexpected_statement of string
exception Ghost_var_in_global_decl
              of Expr.varId * Expr.sort * Expr.initVal_t option * Expr.kind_t
exception Ghost_var_in_local_decl
              of Expr.varId * Expr.sort * Expr.initVal_t option * Expr.kind_t
exception Ghost_vars_in_assignment of Expr.term list
exception Normal_vars_in_ghost_assignment of Expr.term list
exception No_kind_for_var of Expr.varId
exception Duplicated_ranking_function of Vd.node_id_t * Expr.term * Expr.term
exception Ranking_function_unmatched_sort of Expr.sort * Expr.term * Expr.sort
exception Different_argument_length of string * string


let invVars = Hashtbl.create System.initVarNum

let empty_tbl = Hashtbl.create 1

let curr_box_counter = ref 0


(* Looks for a term sort in the global and temporal var tables. *)
let get_sort (t:Expr.term) : Expr.sort =
  let p = Expr.get_var_owner t in
  let gVars = System.get_global !Symtbl.sys in
  let (iVars,lVars) = match p with
                        Some proc -> (System.get_input_by_name !Symtbl.sys proc,
                                      System.get_local_by_name !Symtbl.sys proc)
                      | None      -> (System.empty_var_table,
                                      System.empty_var_table)
  in
    System.get_sort_from_term gVars iVars lVars invVars t


(* Parsing error message funtion *)
let parser_error msg =
  let msg = sprintf "Error at line %i:\n%s" (Global.get_linenum ()) msg in
    raise (ParserError msg)



let parser_typing_error term a_sort get_expr =
  let term_str = (Expr.term_to_str term) in
  let term_sort_str = (Expr.sort_to_str (get_sort term)) in
  let sort_str = (Expr.sort_to_str a_sort) in
  let str_expr = (get_expr ()) in
  let str = sprintf "Term \"%s\" is of sort %s, but it was \
                     expected to be of sort %s in expression \"%s\""
                     term_str term_sort_str sort_str str_expr in
  parser_error str



let parser_types_incompatible t1 t2 get_expr_str =
  let t1_str = (Expr.term_to_str t1) in
  let s1_str = (Expr.sort_to_str (get_sort t1)) in
  let t2_str = (Expr.term_to_str t2) in
  let s2_str = (Expr.sort_to_str (get_sort t2)) in
  let str_expr = (get_expr_str ()) in
  let str = (Printf.sprintf "Unexpectedly \"%s\" is of type \"%s\" and  \
                             \"%s\" is of type \"%s\", when they should \
                             have the same type in expression \"%s\"."
                            t1_str s1_str t2_str s2_str str_expr) in
    parser_error str



let parser_check_compatibility t1 t2 get_expr_str =
  let s1 = get_sort t1 in
  let s2 = get_sort t2 in
    if (s1 != s2) then
      parser_types_incompatible t1 t2 get_expr_str


let parser_check_compatibility_with_op_cond t1 t2 get_expr_str op =
  let s1 = get_sort t1 in
  let s2 = get_sort t2 in
  match op with
    In          -> if (s1 != Expr.Addr || s2 != Expr.Set) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEq    -> if (s1 != Expr.Set || s2 != Expr.Set) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InTh        -> if (s1 != Expr.Thid || s2 != Expr.SetTh) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqTh  -> if (s1 != Expr.SetTh || s2 != Expr.SetTh) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InInt       -> if (s1 != Expr.Int || s2 != Expr.SetInt) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqInt -> if (s1 != Expr.SetInt || s2 != Expr.SetInt) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InElem      -> if (s1 != Expr.Elem || s2 != Expr.SetElem) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqElem-> if (s1 != Expr.SetElem || s2 != Expr.SetElem) then
                     parser_types_incompatible t1 t2 get_expr_str
  | _           -> if (s1 != s2) then
                     parser_types_incompatible t1 t2 get_expr_str


let parser_check_type checker a_term a_sort get_expr_str =
  try 
    checker a_term
  with
    | WrongType(_) -> parser_typing_error a_term a_sort get_expr_str


let decl_inv_var (v:Expr.varId) (s:Expr.sort) (e:Expr.initVal_t option) : unit =
  System.add_var invVars v s e None Expr.Normal



(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id


let check_sort_var (v:Expr.variable) : unit =
  let id = Expr.var_id   v in
  let s  = Expr.var_sort v in
  let p  = Expr.var_proc v in
  let k  = Expr.var_k    v in
  let generic_var = Expr.VarT (Expr.build_var id Expr.Unknown false None p k) in
  let knownSort = get_sort generic_var in
    if (knownSort != s) then
      begin
        Interface.Err.msg "Mismatch variable type" $
          sprintf "Variable %s is of sort %s, while it is trying to be \
                   assigned to an expression of sort %s"
                    id (Expr.sort_to_str knownSort) (Expr.sort_to_str s);
        raise (Sort_mismatch (id, knownSort, s))
      end


let wrong_sort_msg_for (t:Expr.term) (s:Expr.sort) : unit =
  Interface.Err.msg "Wrong type" $
  sprintf "A term of sort %s was expected, but term \"%s\" has sort %s."
              (Expr.sort_to_str s) (Expr.term_to_str t)
              (Expr.sort_to_str (get_sort t))


let parser_check_boolean_type a_term get_expr_str =
  match a_term with
    | Expr.VarT v -> let var = Expr.inject_var_sort v Expr.Bool in
                       check_sort_var var;
                       Expr.boolvar var
    | _           -> parser_typing_error a_term Expr.Bool get_expr_str


let check_type_int t =
  match t with
      Expr.IntT i -> i
    | Expr.VarT v -> let var = Expr.inject_var_sort v Expr.Int in
                       check_sort_var var;
                       Expr.VarInt var
    | _           -> raise (WrongType t)


let check_type_set t =
  match t with
      Expr.SetT s -> s
    | Expr.VarT v -> let var = Expr.inject_var_sort v Expr.Set in
                       check_sort_var var;
                       Expr.VarSet var
    | _           -> raise (WrongType t)


let check_type_elem t =
  match t with
      Expr.ElemT e -> e
    | Expr.VarT v  -> let var = Expr.inject_var_sort v Expr.Elem in
                        check_sort_var var;
                        Expr.VarElem var
    | _            -> raise (WrongType t)


let check_type_thid t =
  match t with
      Expr.ThidT th -> th
    | Expr.VarT v   -> let var = Expr.inject_var_sort v Expr.Thid in
                         check_sort_var var;
                         Expr.VarTh var
    | _             -> raise (WrongType t)


let check_type_addr t =
  match t with
      Expr.AddrT a -> a
    | Expr.VarT v  -> let var = Expr.inject_var_sort v Expr.Addr in
                        check_sort_var var;
                        Expr.VarAddr var
    | _            -> raise (WrongType t)


let check_type_cell t =
  match t with
      Expr.CellT c -> c
    | Expr.VarT v  -> let var = Expr.inject_var_sort v Expr.Cell in
                        check_sort_var var;
                        Expr.VarCell var
    | _            -> raise (WrongType t)


let check_type_setth t =
  match t with
      Expr.SetThT sth -> sth
    | Expr.VarT v     -> let var = Expr.inject_var_sort v Expr.SetTh in
                           check_sort_var var;
                           Expr.VarSetTh var
    | _               -> raise (WrongType t)


let check_type_setint t =
  match t with
      Expr.SetIntT sth -> sth
    | Expr.VarT v      -> let var = Expr.inject_var_sort v Expr.SetInt in
                            check_sort_var var;
                            Expr.VarSetInt var
    | _                -> raise (WrongType t)


let check_type_setelem t =
  match t with
      Expr.SetElemT se -> se
    | Expr.VarT v      -> let var = Expr.inject_var_sort v Expr.SetElem in
                            check_sort_var var;
                            Expr.VarSetElem var
    | _                -> raise (WrongType t)


let check_type_path t =
  match t with
      Expr.PathT p -> p
    | Expr.VarT v  -> let var = Expr.inject_var_sort v Expr.Path in
                        check_sort_var var;
                        Expr.VarPath var
    | _            -> raise (WrongType t)


let check_type_mem t =
  match t with
      Expr.MemT m  -> m
    | Expr.VarT v  -> let var = Expr.inject_var_sort v Expr.Mem in
                        check_sort_var var;
                        Expr.VarMem var
    | _            -> raise (WrongType t)


let check_type_addrarr t =
  match t with
      Expr.AddrArrayT arr -> arr
    | Expr.VarT v         -> let var = Expr.inject_var_sort v Expr.AddrArray in
                               check_sort_var var;
                               Expr.VarAddrArray var
    | _                   -> raise (WrongType t)


let check_type_tidarr t =
  match t with
      Expr.TidArrayT arr -> arr
    | Expr.VarT v        -> let var = Expr.inject_var_sort v Expr.TidArray in
                              check_sort_var var;
                              Expr.VarTidArray var
    | _                  -> raise (WrongType t)



let check_and_get_sort (id:string) : Expr.sort =
  match id with
    "tid"     -> Expr.Thid
  | "elem"    -> Expr.Elem
  | "addr"    -> Expr.Addr
  | "cell"    -> Expr.Cell
  | "mem"     -> Expr.Mem
  | "path"    -> Expr.Path
  | "bool"    -> Expr.Bool
  | "addrSet" -> Expr.Set
  | "tidSet"  -> Expr.SetTh
  | "intSet"  -> Expr.SetInt
  | "int"     -> Expr.Int
  | _ -> begin
           Interface.Err.msg "Unrecognized sort" $
             sprintf "A sort was expected, but \"%s\" was found" id;
           raise (Not_sort_name id)
         end


let check_is_procedure (id:string) =
  if not (System.is_proc !Symtbl.sys id) then
    begin
      Interface.Err.msg "Unknown procedure" $
              sprintf "Identifier \"%s\" is used as a procedure identifier, \
                       but no procedure with such name has been parsed." id;
      raise (Unknown_procedure id)
    end


let inject_sort (exp:Expr.term) : Expr.term =
  match exp with
    Expr.VarT v -> let s = get_sort exp in
                   let var = Expr.inject_var_sort v s in
                     begin
                       match s with
                         Expr.Set       -> Expr.SetT       (Expr.VarSet       var)
                       | Expr.Elem      -> Expr.ElemT      (Expr.VarElem      var)
                       | Expr.Thid      -> Expr.ThidT      (Expr.VarTh        var)
                       | Expr.Addr      -> Expr.AddrT      (Expr.VarAddr      var)
                       | Expr.Cell      -> Expr.CellT      (Expr.VarCell      var)
                       | Expr.SetTh     -> Expr.SetThT     (Expr.VarSetTh     var)
                       | Expr.SetInt    -> Expr.SetIntT    (Expr.VarSetInt    var)
                       | Expr.SetElem   -> Expr.SetElemT   (Expr.VarSetElem   var)
                       | Expr.Path      -> Expr.PathT      (Expr.VarPath      var)
                       | Expr.Mem       -> Expr.MemT       (Expr.VarMem       var)
                       | Expr.Bool      -> Expr.VarT       (var)
                       | Expr.Int       -> Expr.IntT       (Expr.VarInt       var)
                       | Expr.Array     -> Expr.ArrayT     (Expr.VarArray     var)
                       | Expr.AddrArray -> Expr.AddrArrayT (Expr.VarAddrArray var)
                       | Expr.TidArray  -> Expr.TidArrayT  (Expr.VarTidArray  var)
                       | Expr.Unknown   -> Expr.VarT       (var)
                     end
  | _           -> exp


let unexpected_statement get_str_expr =
  let str_expr = (get_str_expr()) in
    Interface.Err.msg "Unexpected statement" $
      sprintf "Ghost and atomic statements admit only assignments or \
               conditional statements. However, the following statement \
               was found:\n\n%s\n" str_expr;
    raise (Unexpected_statement str_expr)


let check_var_belongs_to_procedure (v:Expr.varId) (p_name:string) =
  let p_info = System.get_proc_by_name !Symtbl.sys p_name in
  let iVars = System.proc_info_get_input p_info in
  let lVars = System.proc_info_get_local p_info in
    if not (System.mem_var iVars v || System.mem_var lVars v) then
      begin
        Interface.Err.msg "Variable not declared in procedure" $
                sprintf "Variable \"%s\" does not belong to procedure %s"
                        v p_name;
        raise (Variable_not_in_procedure (v, p_name))
      end


let check_delta_sort (s:Expr.sort) : unit =
  match s with
    Expr.Int    -> ()
  | Expr.Set    -> ()
  | Expr.SetTh  -> ()
  | Expr.SetInt -> ()
  | _        -> Interface.Err.msg "Wrong ranking function sort" $
                  sprintf "By the moment, only expressions of sort %s are \
                           accepted for ranking functions. Instead, an \
                           expression of sort %s was found."
                          (Expr.sort_to_str Expr.Int)
                          (Expr.sort_to_str s)


let check_and_add_delta (tbl:Vd.delta_fun_t)
                        (lst:(Vd.delta_range_t list * Expr.term) list)
                          : unit =
  let sort = ref None in
  let add e k =
    if Hashtbl.mem tbl k then
      begin
        let prev_e = Hashtbl.find tbl k in
        Interface.Err.msg "Node labeled twice" $
          sprintf "Ranking function is trying to associate to node %s the \
                   expression:\n\"%s\",\nbut this node has already been \
                   associated to expression:\n\"%s\"\n"
                   (Vd.PP.node_id_to_str k)
                   (Expr.term_to_str e)
                   (Expr.term_to_str prev_e);
        raise (Duplicated_ranking_function (k,e,prev_e))
      end
    else
      begin
        let e_sort = get_sort e in
        let _ =
          match !sort with
            None   -> let _ = check_delta_sort e_sort in
                        sort := Some e_sort
          | Some s -> if s <> e_sort then
                        begin
                          Interface.Err.msg"Unmatched sort in ranking function"$
                            sprintf "An expression of sort %s was expected, \
                                     but expression \"%s\" has sort %s."                       
                                     (Expr.sort_to_str s)
                                     (Expr.term_to_str e)
                                     (Expr.sort_to_str e_sort);
                          raise (Ranking_function_unmatched_sort (s,e,e_sort))
                        end
        in
          Hashtbl.add tbl k e
      end in
  let _ = List.iter ( fun (rs,expr) ->
            List.iter (fun r ->
              match r with
                Vd.Single n    -> add expr n
              | Vd.Range (m,n) -> let node_list = VD.gen_node_range m n in
                                    List.iter (add expr) node_list
              | Vd.Default     -> add expr Vd.defaultNodeId
            ) rs
          ) lst
  in
    ()



%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token DIAGRAM SUPPORT THREADS BOXES NODES INITIAL EDGES ACCEPTANCE WITH DEFAULT
%token EDGE_ARROW LARGE_EDGE_ARROW

%token BEGIN END

%token ERROR MKCELL DATA NEXT LOCKID LOCK UNLOCK
%token MEMORY_READ
%token DOT COMMA
%token NULL UPDATE
%token LOWEST_ELEM HIGHEST_ELEM
%token EPSILON
%token EMPTYSET UNION INTR SETDIFF
%token EMPTYSETTH UNIONTH INTRTH SETDIFFTH SINGLETH
%token EMPTYSETINT UNIONINT INTRINT SETDIFFINT SINGLEINT
%token EMPTYSETELEM UNIONELEM INTRELEM SETDIFFELEM SINGLEELEM SET2ELEM
%token PATH2SET ADDR2SET GETP FIRSTLOCKED ORDERLIST
%token APPEND REACH
%token IN SUBSETEQ
%token INTH SUBSETEQTH
%token ININT SUBSETEQINT
%token INELEM SUBSETEQELEM
%token SETINTMIN SETINTMAX
%token THREAD
%token OPEN_BRACKET CLOSE_BRACKET
%token OPEN_SET CLOSE_SET
%token OPEN_PAREN CLOSE_PAREN
%token VERTICAL_BAR
%token COLON DOUBLECOLON SEMICOLON EQUALS NOT_EQUALS
%token ASSIGN
%token LOGICAL_AND LOGICAL_OR LOGICAL_NOT LOGICAL_THEN LOGICAL_IFF
%token LOGICAL_TRUE LOGICAL_FALSE
%token DOT
%token ARR_UPDATE

%token INVARIANT FORMULA PARAM
%token AT UNDERSCORE SHARP
%token MATH_PLUS MATH_MINUS MATH_MULT MATH_DIV MATH_LESS MATH_GREATER
%token MATH_LESS_EQ MATH_GREATER_EQ

%token EOF

%nonassoc EQUALS NOT_EQUALS MATH_LESS MATH_GREATER MATH_LESS_EQ MATH_GREATER_EQ
%nonassoc IDENT

%nonassoc ASSIGN

%right LOGICAL_AND
%right LOGICAL_OR
%right LOGICAL_THEN
%nonassoc LOGICAL_NOT

%left UNION INTR SETDIFF
%left UNIONTH INTRTH SETDIFFTH
%left UNIONINT INTRINT SETDIFFINT

%nonassoc IN SUBSETEQ
%nonassoc INTH SUBSETEQTH
%nonassoc ININT SUBSETEQINT
%nonassoc INELEM SUBSETEQELEM


%nonassoc GHOST_DELIMITER
%nonassoc OPEN_BRACKET CLOSE_BRACKET
%nonassoc OPEN_PAREN CLOSE_PAREN
%nonassoc VERTICAL_BAR


%left MATH_PLUS MATH_MINUS
%left MATH_MULT MATH_DIV
%right MATH_NEG

%left DOT



%start invariant
%start vd_formula
%start diagram
%start param_diagram
%start formula
%start single_formula

%type <System.var_table_t * Expression.formula> single_formula
%type <System.var_table_t * Tag.f_tag option * Expression.formula> invariant
%type <System.var_table_t * Tag.f_tag option * Expression.formula> vd_formula
%type <unit> inv_var_declarations
%type <unit> inv_var_decl_list
%type <unit> inv_var_decl
%type <Tag.f_tag option> formula_tag

%type <Expr.term list> term_list

%type <Expression.formula> formula
%type <Expr.tid option> opt_th_param
%type <Expr.tid option> th_param
%type <Expr.literal> literal
%type <Expr.term> term
%type <Expr.cell> cell
%type <Expr.tid> thid
%type <Expr.elem> elem
%type <Expr.addr> addr
%type <Expr.mem> mem
%type <Expr.path> path
%type <Expr.set> set
%type <Expr.setth> setth
%type <Expr.setint> setint
%type <Expr.setelem> setelem
%type <Expr.integer> integer
%type <Expr.literal> literal
%type <Expr.eq> equals
%type <Expr.diseq> disequals
%type <Expr.term> arrays

%type <Diagrams.vd_t> diagram
%type <(Diagrams.pvd_t * Expression.tid list)> param_diagram
%type <Expr.formula list> support
%type <Expr.formula list> sup_formula_list

%type <Vd.box_t list> boxes
%type <Vd.box_t list> box_list
%type <Vd.box_t> box
%type <Vd.node_t list> nodes
%type <Vd.node_t list> node_list
%type <Vd.node_t> node
%type <Vd.node_id_t> node_id
%type <Vd.node_id_t list> node_id_list
%type <Vd.node_id_t list> initials
%type <Vd.edge_t list> edges
%type <Vd.edge_t list> edge_list
%type <Vd.edge_t> edge
%type <Vd.trans_t> transition
%type <Vd.trans_t list> tran_list
%type <Vd.acceptance_list_t> acceptance
%type <Vd.acceptance_pair_t list> accept_list
%type <Vd.acceptance_pair_t> accept_pair
%type <(Vd.node_id_t * Vd.node_id_t) list> edge_id_list
%type <(Vd.node_id_t * Vd.node_id_t)> edge_id

%type <Vd.delta_range_t> delta_node_desc
%type <Vd.delta_range_t list> delta_node_list
%type <Vd.delta_range_t list> delta_node_pos
%type <Vd.delta_range_t list * Expr.term> delta_func
%type <(Vd.delta_range_t list * Expr.term) list> delta_func_list


%%


/******************   DIAGRAMS **********************/


param_diagram :
  | diagram_init COLON IDENT support nodes initials boxes edges acceptance
    {
      let vd_name      = get_name $3 in
      let sup_formulas = $4 in
      let nodes        = $5 in
      let initial      = $6 in
      let boxes        = $7 in
      let edges        = $8 in
      let accept       = $9 in
        (* By now, we verify that the formula expression written here
           uses variables from V due to the way in which the parser
           is constructed. In the future, if the parser is modified,
           it may be necessary to verify that variables appearing in
           this formula are contained into V *)
        (* I think we must now do this verification, as the program
           is now parsed with statement_parser *)
        VD.new_param_diagram vd_name sup_formulas nodes initial boxes edges accept
    }


diagram :
  | diagram_init COLON IDENT
    THREADS COLON NUMBER
    nodes initials edges acceptance
    {
      let vd_name = get_name $3 in
      let th_num  = $6 in
      let nodes   = $7 in
      let initial = $8 in
      let edges   = $9 in
      let accept  = $10 in
        (* By now, we verify that the formula expression written here
           uses variables from V due to the way in which the parser
           is constructed. In the future, if the parser is modified,
           it may be necessary to verify that variables appearing in
           this formula are contained into V *)
        VD.new_diagram vd_name th_num nodes initial edges accept
    }

diagram_init :
  | DIAGRAM
    { }

support :
  |
    { [] }
  | SUPPORT COLON sup_formula_list
    { $3 }

sup_formula_list :
  |
    { [] }
  | formula sup_formula_list
    { $1 :: $2 }


boxes :
  | BOXES COLON box_list
    { $3 }

box_list :
  |
    { [] }
  | box box_list
    { $1 :: $2 }

box :
  | OPEN_SET node_id_list CLOSE_SET COLON IDENT
    {
      let nodes_id = $2 in
      let var_name = get_name $5 in
      let th       = Expr.build_var_tid var_name in
      let _        = incr curr_box_counter in

      VD.new_box !curr_box_counter nodes_id th
    }

nodes :
  | NODES COLON node_list
    { $3 }

node_list :
  |
    { [] }
  | node node_list
    { $1 :: $2 }

node :
  | node_id COLON OPEN_SET formula CLOSE_SET
    {
      let n = $1 in
      let formula = $4 in
        VD.new_node n formula
    }

node_id :
  | OPEN_BRACKET NUMBER CLOSE_BRACKET
    { VD.new_node_id $2 }

initials :
  | INITIAL COLON OPEN_SET node_id_list CLOSE_SET
    { $4 }

node_id_list :
  | NUMBER
    { [VD.new_node_id $1] }
  | NUMBER COMMA node_id_list
    { (VD.new_node_id $1) :: $3 }

edges :
  | EDGES COLON edge_list
    { $3 }

edge_list :
  |
    { [] }
  | edge edge_list
    { $1 :: $2 }

edge :
  | node_id LOGICAL_THEN node_id COLON OPEN_SET tran_list CLOSE_SET
    {
      let from_node = $1 in
      let to_node = $3 in
      let tran_set = $6 in
      let edge_info = VD.new_edge_info Vd.Normal tran_set in
        VD.new_edge from_node to_node edge_info
    }
  | node_id LARGE_EDGE_ARROW node_id COLON OPEN_SET tran_list CLOSE_SET
    {
      let from_node = $1 in
      let to_node = $3 in
      let tran_set = $6 in
      let edge_info = VD.new_edge_info Vd.Large tran_set in
        VD.new_edge from_node to_node edge_info
    }


tran_list :
  |
    { [] }
  | transition
    { [$1] }
  | transition COMMA tran_list
    { $1 :: $3 }


transition :
  | NUMBER opt_th_param
    {
      let pc = $1 in
      let th = $2 in
        VD.new_trans pc th
    }


acceptance :
  | ACCEPTANCE COLON accept_list
    {
      let acc_list = $3 in
      VD.new_acceptance_list acc_list
    }


accept_list :
  |
    { [] }
  | accept_pair accept_list
    { $1 :: $2 }


accept_pair :
  | OPEN_SET edge_id_list CLOSE_SET COLON OPEN_SET edge_id_list CLOSE_SET
    WITH BEGIN delta_func_list END
    {
      let l1 = $2 in
      let l2 = $6 in
      let f_list = $10 in
      let tbl = Hashtbl.create Vd.initNodeNum in
      let _ = check_and_add_delta tbl f_list in

      VD.new_acceptance_pair l1 l2 tbl
    }


edge_id_list :
  |
    { [] }
  | edge_id
    { [$1] }
  | edge_id COMMA edge_id_list
    { $1 :: $3 }


edge_id :
  | node_id LOGICAL_THEN node_id
    {
      let n1 = $1 in
      let n2 = $3 in
      (n1,n2)
    }


delta_func_list :
  | delta_func
    { [$1] }
  | delta_func delta_func_list
    { $1 :: $2 }


delta_func :
  | delta_node_pos COLON term
    {
      let pos_list = $1 in
      let expr = $3 in
        (pos_list, expr)
    }


delta_node_pos :
  | delta_node_list
    { $1 }
  | DEFAULT
    { [Vd.Default] }


delta_node_list :
  | delta_node_desc
    { [$1] }
  | delta_node_desc COMMA delta_node_list
    { $1 :: $3 }


delta_node_desc :
  | NUMBER
    { Vd.Single (VD.new_node_id $1) }
  | NUMBER MATH_MINUS NUMBER
    { Vd.Range (VD.new_node_id $1, VD.new_node_id $3) }


/*********************     SINGLE FORMULA    *************************/


single_formula :
  | param COLON inv_var_declarations FORMULA COLON formula
    { let declPhiVars = System.copy_var_table invVars in
      let phi         = $6 in
      let _           = System.clear_table invVars
      in
        (declPhiVars, phi)
    }


/*********************     INVARIANTS    *************************/

invariant :
  | param COLON inv_var_declarations INVARIANT formula_tag COLON formula
    { let declInvVars = System.copy_var_table invVars in
      let tag         = $5 in
      let inv         = $7 in
      let _           = System.clear_table invVars
      in
        (declInvVars, tag, inv)
    }


vd_formula :
  | param COLON inv_var_declarations FORMULA formula_tag COLON formula
    { let declPhiVars = System.copy_var_table invVars in
      let tag         = $5 in
      let phi         = $7 in
      let _           = System.clear_table invVars
      in
        (declPhiVars, tag, phi)
    }

formula_tag :
  |
    { None }
  | OPEN_BRACKET IDENT CLOSE_BRACKET
    { Some (Tag.new_tag (get_name $2)) }


param :
  | PARAM
    { }


inv_var_declarations:
  |
    { }
  | inv_var_decl_list
    { }


inv_var_decl_list:
  | inv_var_decl
    { () }
  | inv_var_decl inv_var_decl_list
    { () }


inv_var_decl:
  | IDENT IDENT
    {
      let s      = check_and_get_sort (get_name $1) in
      let v_name = get_name $2 in

(*      decl_global_var v_name s None Expr.Normal; *)
      decl_inv_var v_name s None
    }


/***********************    FORMULAS    ************************/



/* FORMULAS */

formula :
  | OPEN_PAREN formula CLOSE_PAREN
      { $2 }
  | literal
      { Expr.Literal $1 }
  | LOGICAL_TRUE
      { Expr.True }
  | LOGICAL_FALSE
      { Expr.False }
  | LOGICAL_NOT formula
      { Expr.Not $2 }
  | formula LOGICAL_AND formula
      { Expr.And ($1, $3) }
  | formula LOGICAL_OR formula
      { Expr.Or ($1, $3) }
  | formula LOGICAL_THEN formula
      { Expr.Implies ($1, $3) }
  | formula EQUALS formula
      { Expr.Iff ($1, $3) }
  | AT NUMBER opt_th_param DOT
      {
        let line_num = $2 in
        let th_p     = $3 in
          Expr.pc_form line_num th_p false
      }
  | AT IDENT opt_th_param DOT
      {
        let label_name = get_name $2 in
        let th_p       = $3 in
        let labelTbl   = System.get_labels !Symtbl.sys in
        let pc_pos     = System.get_label_pos labelTbl label_name in
(*      let pos_list = List.map (fun p -> Expr.pc_form p th_p false) pc_list *)
        let pc_expr    = match pc_pos with
                           None -> parser_error ("Unknown label: " ^ label_name)
                         | Some (i,e) -> if i = e then
                                           Expr.PC (i, th_p, false)
                                         else
                                           Expr.PCRange (i, e, th_p, false)
        in
          Expr.Literal (Expr.Atom pc_expr)
(*          Expr.disj_list pos_list *)
      }


/* THREAD PARAMS */


opt_th_param:
  |
    { None }
  | th_param
    { $1 }


th_param:
  | OPEN_PAREN IDENT CLOSE_PAREN
    {
      let th_id = get_name $2 in
        Some (Expr.build_var_tid th_id)
    }
  | OPEN_BRACKET NUMBER CLOSE_BRACKET
    {
      let th_id = $2 in
        Some (Expr.build_num_tid th_id)
    }



/* LITERALS */

literal :
  | APPEND OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "append(%s,%s,%s)" (Expr.term_to_str $3)
                                                       (Expr.term_to_str $5)
                                                       (Expr.term_to_str $7) in
      let p1   = parser_check_type check_type_path $3 Expr.Path get_str_expr in
      let p2   = parser_check_type check_type_path $5 Expr.Path get_str_expr in
      let pres = parser_check_type check_type_path $7 Expr.Path get_str_expr in
        Expr.Atom (Expr.Append (p1,p2,pres))
    }
  | REACH OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "reach(%s,%s,%s,%s)" (Expr.term_to_str $3)
                                                         (Expr.term_to_str $5)
                                                         (Expr.term_to_str $7)
                                                         (Expr.term_to_str $9) in
      let h      = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 Expr.Addr get_str_expr in
      let p      = parser_check_type check_type_path $9 Expr.Path get_str_expr in
        Expr.Atom (Expr.Reach (h,a_from,a_to,p))
    }
  | REACH OPEN_PAREN term COMMA term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "reach(%s,%s,%s,%s,%s)" (Expr.term_to_str $3)
                                                            (Expr.term_to_str $5)
                                                            (Expr.term_to_str $7)
                                                            (Expr.term_to_str $9)
                                                            (Expr.term_to_str $11) in
      let h      = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 Expr.Addr get_str_expr in
      let p      = parser_check_type check_type_path $9 Expr.Path get_str_expr in
      let l      = parser_check_type check_type_int $11 Expr.Int get_str_expr in
        Expr.Atom (Expr.ReachAt (h,a_from,a_to,l,p))
    }
  | ORDERLIST OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "orderlist(%s,%s,%s)" (Expr.term_to_str $3)
                                                          (Expr.term_to_str $5)
                                                          (Expr.term_to_str $7) in
      let h      = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 Expr.Addr get_str_expr in
        Expr.Atom (Expr.OrderList (h,a_from,a_to))
    }
  | term IN term
    {
      let get_str_expr () = sprintf "%s in %s" (Expr.term_to_str $1)
                                               (Expr.term_to_str $3) in
      let a = parser_check_type check_type_addr $1 Expr.Addr get_str_expr in
      let r = parser_check_type check_type_set  $3 Expr.Set get_str_expr in
        Expr.Atom (Expr.In (a,r))
    }
  | term SUBSETEQ term
    {
      let get_str_expr () = sprintf "%s subseteq %s)" (Expr.term_to_str $1)
                                                      (Expr.term_to_str $3) in
      let s = parser_check_type check_type_set  $1 Expr.Set get_str_expr in
      let r = parser_check_type check_type_set  $3 Expr.Set get_str_expr in
        Expr.Atom (Expr.SubsetEq(s,r))
    }
  | term INTH term
    {
      let get_str_expr () = sprintf "%s inTh %s" (Expr.term_to_str $1)
                                                 (Expr.term_to_str $3) in
      let th = parser_check_type check_type_thid  $1 Expr.Thid get_str_expr in
      let s  = parser_check_type check_type_setth $3 Expr.SetTh get_str_expr in
        Expr.Atom (Expr.InTh (th,s))
    }
  | term SUBSETEQTH term
    {
      let get_str_expr () = sprintf "%s subseteqTh %s" (Expr.term_to_str $1)
                                                       (Expr.term_to_str $3) in
      let r = parser_check_type check_type_setth $1 Expr.SetTh get_str_expr in
      let s = parser_check_type check_type_setth $3 Expr.SetTh get_str_expr in
        Expr.Atom (Expr.SubsetEqTh(r,s))
    }
  | term ININT term
    {
      let get_str_expr () = sprintf "%s inInt %s" (Expr.term_to_str $1)
                                                  (Expr.term_to_str $3) in
      let i = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let s = parser_check_type check_type_setint $3 Expr.SetInt get_str_expr in
        Expr.Atom (Expr.InInt (i,s))
    }
  | term SUBSETEQINT term
    {
      let get_str_expr () = sprintf "%s subseteqInt %s" (Expr.term_to_str $1)
                                                        (Expr.term_to_str $3) in
      let r = parser_check_type check_type_setint $1 Expr.SetInt get_str_expr in
      let s = parser_check_type check_type_setint $3 Expr.SetInt get_str_expr in
        Expr.Atom (Expr.SubsetEqInt(r,s))
    }
  | term INELEM term
    {
      let get_str_expr () = sprintf "%s inElem %s" (Expr.term_to_str $1)
                                                   (Expr.term_to_str $3) in
      let e = parser_check_type check_type_elem $1 Expr.Elem get_str_expr in
      let s = parser_check_type check_type_setelem $3 Expr.SetElem get_str_expr in
        Expr.Atom (Expr.InElem (e,s))
    }
  | term SUBSETEQELEM term
    {
      let get_str_expr () = sprintf "%s subseteqElem %s" (Expr.term_to_str $1)
                                                         (Expr.term_to_str $3) in
      let r = parser_check_type check_type_setelem $1 Expr.SetElem get_str_expr in
      let s = parser_check_type check_type_setelem $3 Expr.SetElem get_str_expr in
        Expr.Atom (Expr.SubsetEqElem(r,s))
    }
  | term MATH_LESS term
    {
      let get_str_expr () = sprintf "%s < %s" (Expr.term_to_str $1)
                                              (Expr.term_to_str $3) in
      try
        let e1 = parser_check_type check_type_elem $1 Expr.Elem get_str_expr in
        let e2 = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
          Expr.Atom (Expr.LessElem (e1, e2))
      with
        _ -> let i1 = parser_check_type check_type_int $1 Expr.Int get_str_expr in
             let i2 = parser_check_type check_type_int $3 Expr.Int get_str_expr in
               Expr.Atom (Expr.Less (i1, i2))
    }
  | term MATH_GREATER term
    {
      let get_str_expr () = sprintf "%s > %s" (Expr.term_to_str $1)
                                              (Expr.term_to_str $3) in
      try
        let e1 = parser_check_type check_type_elem $1 Expr.Elem get_str_expr in
        let e2 = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
          Expr.Atom (Expr.GreaterElem (e1, e2))
      with _ -> let i1 = parser_check_type check_type_int $1 Expr.Int get_str_expr in
                let i2 = parser_check_type check_type_int $3 Expr.Int get_str_expr in
                  Expr.Atom (Expr.Greater (i1, i2))
    }
  | term MATH_LESS_EQ term
    {
      let get_str_expr () = sprintf "%s <= %s" (Expr.term_to_str $1)
                                               (Expr.term_to_str $3) in
      let i1 = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2 = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.Atom (Expr.LessEq (i1, i2))
    }
  | term MATH_GREATER_EQ term
    {
      let get_str_expr () = sprintf "%s >= %s" (Expr.term_to_str $1)
                                               (Expr.term_to_str $3) in
      let i1 = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2 = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.Atom (Expr.GreaterEq (i1, i2))
    }
  | equals
    { Expr.Atom (Expr.Eq($1)) }
  | disequals
    { Expr.Atom (Expr.InEq($1)) }



/* EQUALS */

equals :
  | term EQUALS term
    {
      let get_str_expr () = sprintf "%s = %s" (Expr.term_to_str $1)
                                              (Expr.term_to_str $3) in
      let t1 = $1 in
      let t2 = $3 in

      parser_check_compatibility t1 t2 get_str_expr ;
      (inject_sort t1, inject_sort t2)
    }


/* DISEQUALS */

disequals :
  | term NOT_EQUALS term
    {
      let get_str_expr () = sprintf "%s != %s" (Expr.term_to_str $1)
                                               (Expr.term_to_str $3) in
      let t1= $1 in
      let t2= $3 in

      parser_check_compatibility t1 t2 get_str_expr ;
      (inject_sort t1, inject_sort t2)
    }


/* TERMS */

term :
  | ident
    { $1 }
  | set
    { Expr.SetT($1) }
  | elem
    { Expr.ElemT($1) }
  | thid
    { Expr.ThidT($1) }
  | addr
    { Expr.AddrT($1) }
  | cell
    { Expr.CellT($1) }
  | setth
    { Expr.SetThT($1) }
  | setint
    { Expr.SetIntT($1) }
  | setelem
    { Expr.SetElemT($1) }
  | path
    { Expr.PathT($1) }
  | mem
    { Expr.MemT($1) }
  | integer
    { Expr.IntT($1) }
  | arrays
    { $1 }
  | OPEN_PAREN term CLOSE_PAREN
    { $2 }



/* IDENT */

ident :
  IDENT
    {
      let id  = get_name $1 in
      let var = Expr.build_var id Expr.Unknown false None None Expr.Normal in
        inject_sort (Expr.VarT var)
    }
  | IDENT DOUBLECOLON IDENT th_param
    {

      let proc_name = get_name $1 in

(* Under testing. Possible correction. *)
(*
      let c_proc = if !current_proc <> "" then
                     Some !current_proc
                   else
                     None in
*)
      let id            = get_name $3 in
      let th            = $4 in
      let _             = check_is_procedure proc_name in
      let _             = check_var_belongs_to_procedure id proc_name in

      let proc_info     = System.get_proc_by_name !Symtbl.sys proc_name in
      let iVars         = System.proc_info_get_input proc_info in
      let lVars         = System.proc_info_get_local proc_info in

      let k             = if System.mem_var iVars id then
                            System.find_var_kind iVars id
                          else
                            System.find_var_kind lVars id in
      let var           = inject_sort (Expr.VarT
                            (Expr.build_var id Expr.Unknown false th
                                            (Some proc_name) k))
      in
        var

    }


/* SET terms*/

set :
  | EMPTYSET
    { Expr.EmptySet }
  | OPEN_SET term CLOSE_SET
    {
      let get_str_expr() = sprintf "{ %s }" (Expr.term_to_str $2) in
      let a = parser_check_type check_type_addr $2 Expr.Addr get_str_expr in
        Expr.Singl(a)
    }
  | term UNION term
    {
      let get_str_expr() = sprintf "%s Union %s" (Expr.term_to_str $1)
                                                 (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_set  $1 Expr.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $3 Expr.Set get_str_expr in
        Expr.Union(s1,s2)
    }
  | term INTR term
    {
      let get_str_expr() = sprintf "%s Intr %s" (Expr.term_to_str $1)
                                                (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_set  $1 Expr.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $3 Expr.Set get_str_expr in
        Expr.Intr(s1,s2)
    }
  | term SETDIFF term
    {
      let get_str_expr() = sprintf "%s SetDiff %s" (Expr.term_to_str $1)
                                                   (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_set  $1 Expr.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $3 Expr.Set get_str_expr in
        Expr.Setdiff(s1,s2)
    }
  | PATH2SET OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "path2set(%s)" (Expr.term_to_str $3) in
      let p = parser_check_type check_type_path $3 Expr.Path get_str_expr in
        Expr.PathToSet(p)
    }
  | ADDR2SET OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "addr2set(%s,%s)" (Expr.term_to_str $3)
                                                      (Expr.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
        Expr.AddrToSet(h,a)
    }


/* ELEM terms */

elem :
  | term DOT DATA
    {
      let get_str_expr () = sprintf "%s.data" (Expr.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 Expr.Cell get_str_expr in
        Expr.CellData(c)
    }
  | LOWEST_ELEM
    {
      Expr.LowestElem
    }
  | HIGHEST_ELEM
    {
      Expr.HighestElem
    }


/* THID terms */

thid :
  | term DOT LOCKID
    {
      let get_str_expr () = sprintf "%s.lockid" (Expr.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 Expr.Cell get_str_expr in
        Expr.CellLockId(c)
    }
  | SHARP
    { Expr.NoThid }


/* ADDR terms */

addr :
  | NULL
    { Expr.Null }
  | term DOT NEXT
    {
      let get_str_expr () = sprintf "%s.data" (Expr.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 Expr.Cell get_str_expr in
        Expr.Next(c)
    }
  | FIRSTLOCKED OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "firstlocked(%s,%s)" (Expr.term_to_str $3)
                                                         (Expr.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let p = parser_check_type check_type_path $5 Expr.Path get_str_expr in
        Expr.FirstLocked(h,p)
    }
  | FIRSTLOCKED OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "firstlocked(%s,%s,%s)"
                                          (Expr.term_to_str $3)
                                          (Expr.term_to_str $5)
                                          (Expr.term_to_str $7) in
      let h = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let p = parser_check_type check_type_path $5 Expr.Path get_str_expr in
      let l = parser_check_type check_type_int $7 Expr.Int get_str_expr in
        Expr.FirstLockedAt(h,p,l)
    }

/* CELL terms */

cell :
  | ERROR
    { Expr.Error }
  | MKCELL OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "mkcell(%s,%s,%s)"
                                           (Expr.term_to_str $3)
                                           (Expr.term_to_str $5)
                                           (Expr.term_to_str $7) in
      let d  = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
      let a  = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let th = parser_check_type check_type_thid $7 Expr.Thid get_str_expr in
        Expr.MkCell(d,a,th)
    }
  | MKCELL OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "mkcell(%s,%s,%s,%s)"
                                           (Expr.term_to_str $3)
                                           (Expr.term_to_str $5)
                                           (Expr.term_to_str $7)
                                           (Expr.term_to_str $9) in
      let e  = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
      let aa = parser_check_type check_type_addrarr $5 Expr.AddrArray get_str_expr in
      let ta = parser_check_type check_type_tidarr $7 Expr.TidArray get_str_expr in
      let l  = parser_check_type check_type_int $9 Expr.Int get_str_expr in
        Expr.MkSLCell(e,aa,ta,l)
    }
  | MKCELL OPEN_PAREN term COMMA
                      OPEN_BRACKET term_list CLOSE_BRACKET COMMA
                      OPEN_BRACKET term_list CLOSE_BRACKET COMMA
                      term CLOSE_PAREN
    {
      let list_term_to_str ts = String.concat "," (List.map Expr.term_to_str ts) in
      let addrs_str = list_term_to_str $6 in
      let tids_str = list_term_to_str $10 in
      let get_str_expr () = sprintf "mkcell(%s,[%s],[%s],%s)"
                                           (Expr.term_to_str $3)
                                           (addrs_str)
                                           (tids_str)
                                           (Expr.term_to_str $13) in
      let e  = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
      let addrs = List.map (fun a ->
                    parser_check_type check_type_addr a Expr.Addr get_str_expr
                  ) $6 in
      let tids = List.map (fun t ->
                   parser_check_type check_type_thid t Expr.Thid get_str_expr
                 ) $10 in
      let l  = parser_check_type check_type_int $13 Expr.Int get_str_expr in
      if List.length addrs <> List.length tids then
        begin
          Interface.Err.msg "Different argument lengths" $
            sprintf "mkcell is invoked with an unequal number of addresses [%s] \
                     and thread ids [%s]." addrs_str tids_str;
          raise (Different_argument_length (addrs_str,tids_str))
        end
      else
        Expr.MkSLKCell(e,addrs,tids,l)
    }


  | term DOT LOCK
    {
      let get_str_expr () = sprintf "%s.lock" (Expr.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 Expr.Cell get_str_expr in
        Expr.CellLock(c)
    }
  | term DOT UNLOCK
    {
      let get_str_expr () = sprintf "%s.unlock" (Expr.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 Expr.Cell get_str_expr in
        Expr.CellUnlock(c)
    }
  | MEMORY_READ OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "%s [ %s ]" (Expr.term_to_str $3)
                                                (Expr.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
        Expr.CellAt(h,a)
    }


term_list :
  | term COMMA term
    { [$1;$3] }
  | term COMMA term_list
    { $1 :: $3 }



/* SETTH terms*/

setth :
  | EMPTYSETTH
  { Expr.EmptySetTh }
  | SINGLETH OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleTh(%s)" (Expr.term_to_str $3) in
      let th = parser_check_type check_type_thid  $3 Expr.Thid get_str_expr in
        Expr.SinglTh(th)
    }
  | term UNIONTH term
    {
      let get_str_expr() = sprintf "%s UnionTh %s" (Expr.term_to_str $1)
                                                   (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_setth  $1 Expr.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $3 Expr.SetTh get_str_expr in
        Expr.UnionTh(s1,s2)
    }
  | term INTRTH term
    {
      let get_str_expr() = sprintf "%s IntrTh %s" (Expr.term_to_str $1)
                                                  (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_setth  $1 Expr.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $3 Expr.SetTh get_str_expr in
        Expr.IntrTh(s1,s2)
    }
  | term SETDIFFTH term
    {
      let get_str_expr() = sprintf "%s SetDiffTh %s" (Expr.term_to_str $1)
                                                     (Expr.term_to_str $3) in
      let s1 = parser_check_type check_type_setth  $1 Expr.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $3 Expr.SetTh get_str_expr in
        Expr.SetdiffTh(s1,s2)
    }


/* SETINT terms*/
setint :
  | EMPTYSETINT
     { Expr.EmptySetInt }
  | SINGLEINT OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleInt(%s)" (Expr.term_to_str $3) in
      let th = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.SinglInt(th)
    }
  | UNIONINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "UnionInt(%s,%s)" (Expr.term_to_str $3)
                                                     (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setint  $3 Expr.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint  $5 Expr.SetInt get_str_expr in
        Expr.UnionInt(s1,s2)
    }
  | INTRINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "IntrInt(%s,%s)" (Expr.term_to_str $3)
                                                    (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setint  $3 Expr.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint  $5 Expr.SetInt get_str_expr in
        Expr.IntrInt(s1,s2)
    }
  | SETDIFFINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiffInt(%s,%s)" (Expr.term_to_str $3)
                                                       (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setint $3 Expr.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint $5 Expr.SetInt get_str_expr in
        Expr.SetdiffInt(s1,s2)
    }


/* SETELEM terms*/
setelem :
  | EMPTYSETELEM
     { Expr.EmptySetElem }
  | SINGLEELEM OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleElem(%s)" (Expr.term_to_str $3) in
      let e = parser_check_type check_type_elem $3 Expr.Elem get_str_expr in
        Expr.SinglElem(e)
    }
  | UNIONELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "UnionElem(%s,%s)" (Expr.term_to_str $3)
                                                      (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 Expr.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 Expr.SetElem get_str_expr in
        Expr.UnionElem(s1,s2)
    }
  | INTRELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "IntrElem(%s,%s)" (Expr.term_to_str $3)
                                                     (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 Expr.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 Expr.SetElem get_str_expr in
        Expr.IntrElem(s1,s2)
    }
  | SETDIFFELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiffElem(%s,%s)" (Expr.term_to_str $3)
                                                        (Expr.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 Expr.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 Expr.SetElem get_str_expr in
        Expr.SetdiffElem(s1,s2)
    }
  | SET2ELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "set2elem(%s,%s)" (Expr.term_to_str $3)
                                                      (Expr.term_to_str $5) in
      let m = parser_check_type check_type_mem $3 Expr.Mem get_str_expr in
      let s = parser_check_type check_type_set $5 Expr.Set get_str_expr in
        Expr.SetToElems(s,m)
    }


/* PATH terms */

path :
  | EPSILON
    { Expr.Epsilon }
  | OPEN_BRACKET term CLOSE_BRACKET
    {
      let get_str_expr () = sprintf "[ %s ]" (Expr.term_to_str $2) in
      let a = parser_check_type check_type_addr $2 Expr.Addr get_str_expr in
        Expr.SimplePath(a)
    }
  | GETP OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "getp(%s,%s,%s)" (Expr.term_to_str $3)
                                                     (Expr.term_to_str $5)
                                                     (Expr.term_to_str $7) in
      let h     = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let first = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let last  = parser_check_type check_type_addr $7 Expr.Addr get_str_expr in
        Expr.GetPath(h,first,last)
    }
  | GETP OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "getp(%s,%s,%s,%s)" (Expr.term_to_str $3)
                                                        (Expr.term_to_str $5)
                                                        (Expr.term_to_str $7)
                                                        (Expr.term_to_str $9) in
      let h     = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let first = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let last  = parser_check_type check_type_addr $7 Expr.Addr get_str_expr in
      let l     = parser_check_type check_type_int $9 Expr.Int get_str_expr in
        Expr.GetPathAt(h,first,last,l)
  }


/* MEM terms */

mem :
  | UPDATE OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "update(%s,%s,%s)" (Expr.term_to_str $3)
                                                       (Expr.term_to_str $5)
                                                       (Expr.term_to_str $7) in
      let h = parser_check_type check_type_mem  $3 Expr.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
      let c = parser_check_type check_type_cell $7 Expr.Cell get_str_expr in
        Expr.Update(h,a,c)
    }


/* INTEGER terms*/

integer :
  | NUMBER
    { Expr.IntVal $1 }
  | MATH_MINUS term %prec MATH_NEG
    {
      let get_str_expr () = sprintf "-%s" (Expr.term_to_str $2) in
      let i  = parser_check_type check_type_int $2 Expr.Int get_str_expr in
        Expr.IntNeg i
    }
  | term MATH_PLUS term
    {
      let get_str_expr () = sprintf "%s+%s" (Expr.term_to_str $1)
                                            (Expr.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.IntAdd (i1,i2)
    }
  | term MATH_MINUS term
    {
      let get_str_expr () = sprintf "%s-%s" (Expr.term_to_str $1)
                                            (Expr.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.IntSub (i1,i2)
    }
  | term MATH_MULT term
    {
      let get_str_expr () = sprintf "%s*%s" (Expr.term_to_str $1)
                                            (Expr.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.IntMul (i1,i2)
    }
  | term MATH_DIV term
    {
      let get_str_expr () = sprintf "%s/%s" (Expr.term_to_str $1)
                                            (Expr.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 Expr.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 Expr.Int get_str_expr in
        Expr.IntDiv (i1,i2)
    }
  | SETINTMIN OPEN_PAREN term CLOSE_PAREN
    {
      let iSet = $3 in
      let get_str_expr () = sprintf "setIntMin(%s)" (Expr.term_to_str iSet) in
      let s  = parser_check_type check_type_setint iSet Expr.SetInt get_str_expr
      in
        Expr.IntSetMin (s)
    }
  | SETINTMAX OPEN_PAREN term CLOSE_PAREN
    {
      let iSet = $3 in
      let get_str_expr () = sprintf "setIntMax(%s)" (Expr.term_to_str iSet) in
      let s  = parser_check_type check_type_setint iSet Expr.SetInt get_str_expr
      in
        Expr.IntSetMax (s)
    }



/* ARRAY terms */
arrays :
  | term OPEN_BRACKET term CLOSE_BRACKET
    {
      let get_str_expr () = sprintf "%s[%s]" (Expr.term_to_str $1)
                                             (Expr.term_to_str $3) in
      let i = parser_check_type check_type_int $3 Expr.Int get_str_expr in
      try
        let at = parser_check_type check_type_tidarr $1 Expr.TidArray get_str_expr in
          Expr.ThidT (Expr.ThidArrRd (at,i))
      with _ -> try
        let aa = parser_check_type check_type_addrarr $1 Expr.AddrArray get_str_expr in
          Expr.AddrT (Expr.AddrArrRd (aa,i))
      with e -> try
        let t = parser_check_type check_type_thid $1 Expr.Thid get_str_expr in
        match t with
        | Expr.CellLockId c -> Expr.ThidT (Expr.CellLockIdAt (c,i))
        | _                 -> raise e
      with e -> try
        let a = parser_check_type check_type_addr $1 Expr.Addr get_str_expr in
        match a with
        | Expr.Next c -> Expr.AddrT (Expr.NextAt (c,i))
        | _           -> raise e
      with e ->
        let c = parser_check_type check_type_cell $1 Expr.Cell get_str_expr in
        match c with
        | Expr.CellLock d   -> Expr.CellT (Expr.CellLockAt (d,i))
        | Expr.CellUnlock d -> Expr.CellT (Expr.CellUnlockAt (d,i))
        | _                 -> raise e
    }
  | ARR_UPDATE OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "arrUpd (%s,%s,%s)" (Expr.term_to_str $3)
                                                        (Expr.term_to_str $5)
                                                        (Expr.term_to_str $7) in
      let i = parser_check_type check_type_int $5 Expr.Int get_str_expr in
      try
        let at = parser_check_type check_type_tidarr $3 Expr.TidArray get_str_expr in
        let t = parser_check_type check_type_thid $5 Expr.Thid get_str_expr in
          Expr.TidArrayT (Expr.TidArrayUp (at,i,t))
      with _ ->
        let aa = parser_check_type check_type_addrarr $3 Expr.AddrArray get_str_expr in
        let a = parser_check_type check_type_addr $5 Expr.Addr get_str_expr in
          Expr.AddrArrayT (Expr.AddrArrayUp (aa,i,a))
    }
