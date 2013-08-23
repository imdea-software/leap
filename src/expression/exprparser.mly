%{
open Printf

open LeapLib
open Global

module E      = Expression
module Symtbl = Exprsymtable

(* This code should be changed in the future *)
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


exception WrongType of E.term
exception Sort_mismatch of E.varId * E.sort * E.sort
exception Boolean_var_expected of E.term
exception Not_sort_name of string
exception Duplicated_local_var of E.varId * E.sort
exception No_main
exception Unknown_procedure of string
exception Variable_not_in_procedure of E.varId * string
exception Wrong_assignment of E.term
exception Atomic_double_assignment of E.expr_t
exception Unexpected_statement of string
exception Ghost_var_in_global_decl
              of E.varId * E.sort * E.initVal_t option * E.var_nature
exception Ghost_var_in_local_decl
              of E.varId * E.sort * E.initVal_t option * E.var_nature
exception Ghost_vars_in_assignment of E.term list
exception Normal_vars_in_ghost_assignment of E.term list
exception No_kind_for_var of E.varId
exception Ranking_function_unmatched_sort of E.sort * E.term * E.sort
exception Different_argument_length of string * string


let invVars = Hashtbl.create System.initVarNum

let empty_tbl = Hashtbl.create 1

let curr_box_counter = ref 0


(* Looks for a term sort in the global and temporal var tables. *)
let get_sort (t:E.term) : E.sort =
  let p = E.get_var_owner t in
  let gVars = System.get_global !Symtbl.sys in
  let (iVars,lVars) = match p with
                        E.Scope proc  -> (System.get_input_by_name !Symtbl.sys proc,
                                             System.get_local_by_name !Symtbl.sys proc)
                      | E.GlobalScope -> (System.empty_var_table,
                                             System.empty_var_table)
  in
    System.get_sort_from_term gVars iVars lVars invVars t


(* Parsing error message funtion *)
let parser_error msg =
  let msg = sprintf "Error at line %i:\n%s" (Global.get_linenum ()) msg in
    raise(ParserError msg)



let parser_typing_error term a_sort get_expr =
  let term_str = (E.term_to_str term) in
  let term_sort_str = (E.sort_to_str (get_sort term)) in
  let sort_str = (E.sort_to_str a_sort) in
  let str_expr = (get_expr ()) in
  let str = sprintf "Term \"%s\" is of sort %s, but it was \
                     expected to be of sort %s in expression \"%s\""
                     term_str term_sort_str sort_str str_expr in
  parser_error str



let parser_types_incompatible t1 t2 get_expr_str =
  let t1_str = (E.term_to_str t1) in
  let s1_str = (E.sort_to_str (get_sort t1)) in
  let t2_str = (E.term_to_str t2) in
  let s2_str = (E.sort_to_str (get_sort t2)) in
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
    In          -> if (s1 != E.Addr || s2 != E.Set) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEq    -> if (s1 != E.Set || s2 != E.Set) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InTh        -> if (s1 != E.Tid || s2 != E.SetTh) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqTh  -> if (s1 != E.SetTh || s2 != E.SetTh) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InInt       -> if (s1 != E.Int || s2 != E.SetInt) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqInt -> if (s1 != E.SetInt || s2 != E.SetInt) then
                     parser_types_incompatible t1 t2 get_expr_str
  | InElem      -> if (s1 != E.Elem || s2 != E.SetElem) then
                     parser_types_incompatible t1 t2 get_expr_str
  | SubsetEqElem-> if (s1 != E.SetElem || s2 != E.SetElem) then
                     parser_types_incompatible t1 t2 get_expr_str
  | _           -> if (s1 != s2) then
                     parser_types_incompatible t1 t2 get_expr_str


let parser_check_type checker a_term a_sort get_expr_str =
  try 
    checker a_term
  with
    | WrongType(_) -> parser_typing_error a_term a_sort get_expr_str


let decl_inv_var (v:E.varId) (s:E.sort) (e:E.initVal_t option) : unit =
  System.add_var invVars v s e E.Shared E.RealVar



(* slow way to project: traverse one time per entry *)
let get_name id = fst id
let get_line id = snd id


let check_sort_var (v:E.variable) : unit =
  let generic_var = E.VarT (E.build_var (E.var_id v) E.Unknown false E.Shared
                                        (E.var_scope v) (E.var_nature v)) in
  let knownSort = get_sort generic_var in
    if (knownSort != (E.var_sort v)) then
      begin
        Interface.Err.msg "Mismatch variable type" $
          sprintf "Variable %s is of sort %s, while it is trying to be \
                   assigned to an expression of sort %s"
                    (E.var_id v) (E.sort_to_str knownSort) (E.sort_to_str (E.var_sort v));
        raise(Sort_mismatch((E.var_id v),knownSort,(E.var_sort v)))
      end


let wrong_sort_msg_for (t:E.term) (s:E.sort) : unit =
  Interface.Err.msg "Wrong type" $
  sprintf "A term of sort %s was expected, but term \"%s\" has sort %s."
              (E.sort_to_str s) (E.term_to_str t)
              (E.sort_to_str (get_sort t))


let parser_check_boolean_type a_term get_expr_str =
  match a_term with
    | E.VarT v -> let var = E.inject_var_sort v E.Bool in
                       check_sort_var var;
                       E.boolvar var
    | _           -> parser_typing_error a_term E.Bool get_expr_str


let check_type_int t =
  match t with
      E.IntT i -> i
    | E.VarT v -> let var = E.inject_var_sort v E.Int in
                       check_sort_var var;
                       E.VarInt var
    | _           -> raise(WrongType t)


let check_type_set t =
  match t with
      E.SetT s -> s
    | E.VarT v -> let var = E.inject_var_sort v E.Set in
                       check_sort_var var;
                       E.VarSet var
    | _           -> raise(WrongType t)


let check_type_elem t =
  match t with
      E.ElemT e -> e
    | E.VarT v  -> let var = E.inject_var_sort v E.Elem in
                        check_sort_var var;
                        E.VarElem var
    | _            -> raise(WrongType t)


let check_type_thid t =
  match t with
      E.TidT th -> th
    | E.VarT v   -> let var = E.inject_var_sort v E.Tid in
                         check_sort_var var;
                         E.VarTh var
    | _             -> raise(WrongType t)


let check_type_addr t =
  match t with
      E.AddrT a -> a
    | E.VarT v  -> let var = E.inject_var_sort v E.Addr in
                        check_sort_var var;
                        E.VarAddr var
    | _            -> raise(WrongType t)


let check_type_cell t =
  match t with
      E.CellT c -> c
    | E.VarT v  -> let var = E.inject_var_sort v E.Cell in
                        check_sort_var var;
                        E.VarCell var
    | _            -> raise(WrongType t)


let check_type_setth t =
  match t with
      E.SetThT sth -> sth
    | E.VarT v     -> let var = E.inject_var_sort v E.SetTh in
                           check_sort_var var;
                           E.VarSetTh var
    | _               -> raise(WrongType t)


let check_type_setint t =
  match t with
      E.SetIntT sth -> sth
    | E.VarT v      -> let var = E.inject_var_sort v E.SetInt in
                            check_sort_var var;
                            E.VarSetInt var
    | _                -> raise(WrongType t)


let check_type_setelem t =
  match t with
      E.SetElemT se -> se
    | E.VarT v      -> let var = E.inject_var_sort v E.SetElem in
                            check_sort_var var;
                            E.VarSetElem var
    | _                -> raise(WrongType t)


let check_type_path t =
  match t with
      E.PathT p -> p
    | E.VarT v  -> let var = E.inject_var_sort v E.Path in
                        check_sort_var var;
                        E.VarPath var
    | _            -> raise(WrongType t)


let check_type_mem t =
  match t with
      E.MemT m  -> m
    | E.VarT v  -> let var = E.inject_var_sort v E.Mem in
                        check_sort_var var;
                        E.VarMem var
    | _            -> raise(WrongType t)


let check_type_addrarr t =
  match t with
      E.AddrArrayT arr -> arr
    | E.VarT v         -> let var = E.inject_var_sort v E.AddrArray in
                               check_sort_var var;
                               E.VarAddrArray var
    | _                   -> raise(WrongType t)


let check_type_tidarr t =
  match t with
      E.TidArrayT arr -> arr
    | E.VarT v        -> let var = E.inject_var_sort v E.TidArray in
                              check_sort_var var;
                              E.VarTidArray var
    | _                  -> raise(WrongType t)



let check_and_get_sort (id:string) : E.sort =
  match id with
    "tid"     -> E.Tid
  | "elem"    -> E.Elem
  | "addr"    -> E.Addr
  | "cell"    -> E.Cell
  | "mem"     -> E.Mem
  | "path"    -> E.Path
  | "bool"    -> E.Bool
  | "addrSet" -> E.Set
  | "tidSet"  -> E.SetTh
  | "intSet"  -> E.SetInt
  | "elemSet" -> E.SetElem
  | "int"     -> E.Int
  | "array"   -> E.Array
  | "addrarr" -> E.AddrArray
  | "tidarr"  -> E.TidArray
  | _ -> begin
           Interface.Err.msg "Unrecognized sort" $
             sprintf "A sort was expected, but \"%s\" was found" id;
           raise(Not_sort_name id)
         end


let check_is_procedure (id:string) =
  if not (System.is_proc !Symtbl.sys id) then
    begin
      Interface.Err.msg "Unknown procedure" $
              sprintf "Identifier \"%s\" is used as a procedure identifier, \
                       but no procedure with such name has been parsed." id;
      raise(Unknown_procedure id)
    end


let inject_sort (exp:E.term) : E.term =
  match exp with
    E.VarT v -> let s = get_sort exp in
                   let var = E.inject_var_sort v s in
                     begin
                       match s with
                         E.Set       -> E.SetT       (E.VarSet       var)
                       | E.Elem      -> E.ElemT      (E.VarElem      var)
                       | E.Tid      -> E.TidT      (E.VarTh        var)
                       | E.Addr      -> E.AddrT      (E.VarAddr      var)
                       | E.Cell      -> E.CellT      (E.VarCell      var)
                       | E.SetTh     -> E.SetThT     (E.VarSetTh     var)
                       | E.SetInt    -> E.SetIntT    (E.VarSetInt    var)
                       | E.SetElem   -> E.SetElemT   (E.VarSetElem   var)
                       | E.Path      -> E.PathT      (E.VarPath      var)
                       | E.Mem       -> E.MemT       (E.VarMem       var)
                       | E.Bool      -> E.VarT       (var)
                       | E.Int       -> E.IntT       (E.VarInt       var)
                       | E.Array     -> E.ArrayT     (E.VarArray     var)
                       | E.AddrArray -> E.AddrArrayT (E.VarAddrArray var)
                       | E.TidArray  -> E.TidArrayT  (E.VarTidArray  var)
                       | E.Unknown   -> E.VarT       (var)
                     end
  | _           -> exp


let unexpected_statement get_str_expr =
  let str_expr = (get_str_expr()) in
    Interface.Err.msg "Unexpected statement" $
      sprintf "Ghost and atomic statements admit only assignments or \
               conditional statements. However, the following statement \
               was found:\n\n%s\n" str_expr;
    raise(Unexpected_statement str_expr)


let check_var_belongs_to_procedure (v:E.varId) (p_name:string) =
  let p_info = System.get_proc_by_name !Symtbl.sys p_name in
  let iVars = System.proc_info_get_input p_info in
  let lVars = System.proc_info_get_local p_info in
    if not (System.mem_var iVars v || System.mem_var lVars v) then
      begin
        Interface.Err.msg "Variable not declared in procedure" $
                sprintf "Variable \"%s\" does not belong to procedure %s"
                        v p_name;
        raise(Variable_not_in_procedure(v,p_name))
      end


let check_delta_sort (s:E.sort) : unit =
  match s with
    E.Int    -> ()
  | E.Set    -> ()
  | E.SetTh  -> ()
  | E.SetInt -> ()
  | _        -> Interface.Err.msg "Wrong ranking function sort" $
                  sprintf "By the moment, only expressions of sort %s are \
                           accepted for ranking functions. Instead, an \
                           expression of sort %s was found."
                          (E.sort_to_str E.Int)
                          (E.sort_to_str s)

(*
let check_and_add_delta (tbl:Vd.delta_fun_t)
                        (lst:(Vd.delta_range_t list * E.term) list)
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
                   (E.term_to_str e)
                   (E.term_to_str prev_e);
        raise(Duplicated_ranking_function(k,e,prev_e))
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
                                     (E.sort_to_str s)
                                     (E.term_to_str e)
                                     (E.sort_to_str e_sort);
                          raise(Ranking_function_unmatched_sort(s,e,e_sort))
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
*)

let define_ident (proc_name:E.procedure_name)
                 (id:string)
                 (th:E.shared_or_local) : E.term =
      let k = match proc_name with
              | E.Scope p ->     check_is_procedure p;
                                    check_var_belongs_to_procedure id p;
                                    let proc_info = System.get_proc_by_name !Symtbl.sys p in
                                    let iVars     = System.proc_info_get_input proc_info in
                                    let lVars     = System.proc_info_get_local proc_info in
                                    if System.mem_var iVars id then
                                      System.find_var_kind iVars id
                                    else
                                      System.find_var_kind lVars id
              | E.GlobalScope -> try
                                      let gVars = System.get_global !Symtbl.sys in
                                        System.find_var_kind gVars id
                                    with _ -> E.RealVar in
      inject_sort (E.VarT (E.build_var id E.Unknown false th proc_name k))


%}
%token <string*int> IDENT  // second param is line number
%token <int> NUMBER

%token DIAGRAM SUPPORT THREADS BOXES NODES INITIAL EDGES ACCEPTANCE USING DEFAULT
%token EDGE_ARROW LARGE_EDGE_ARROW

%token BEGIN END

%token ERROR MKCELL DATA NEXT ARR TIDS MAX LOCKID LOCK UNLOCK LOCKAT UNLOCKAT
%token NEXTAT
%token MEMORY_READ
%token DOT COMMA
%token NULL UPDATE
%token LOWEST_ELEM HIGHEST_ELEM
%token EPSILON
%token EMPTYSET UNION INTR SETDIFF
%token EMPTYSETTH UNIONTH INTRTH SETDIFFTH SINGLETH
%token EMPTYSETINT UNIONINT INTRINT SETDIFFINT SINGLEINT
%token EMPTYSETELEM UNIONELEM INTRELEM SETDIFFELEM SINGLEELEM SET2ELEM
%token PATH2SET ADDR2SET GETP FIRSTLOCKED ORDERLIST SKIPLIST
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

%token INVARIANT FORMULA VARS
%token AT UNDERSCORE SHARP
%token MATH_PLUS MATH_MINUS MATH_MULT MATH_DIV MATH_LESS MATH_GREATER
%token MATH_LESS_EQ MATH_GREATER_EQ


%token TID_CONSTRAINT RHO GOAL TRANSITION_TID LINE


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
%start formula
%start single_formula
%start vc_info

%type <Tactics.vc_info> vc_info

%type <System.var_table_t * Expression.formula> single_formula
%type <System.var_table_t * Tag.f_tag option * Expression.formula> invariant
%type <unit> inv_var_declarations
%type <unit> inv_var_decl_list
%type <unit> inv_var_decl
%type <Tag.f_tag option> formula_tag

%type <E.term list> term_list

%type <Expression.formula> formula
%type <E.shared_or_local> opt_th_param
%type <E.shared_or_local> th_param
%type <E.literal> literal
%type <E.term> term
%type <E.cell> cell
%type <E.tid> thid
%type <E.elem> elem
%type <E.addr> addr
%type <E.mem> mem
%type <E.path> path
%type <E.set> set
%type <E.setth> setth
%type <E.setint> setint
%type <E.setelem> setelem
%type <E.integer> integer
%type <E.literal> literal
%type <E.eq> equals
%type <E.diseq> disequals
%type <E.term> arrays
%type <E.addrarr> addrarr
%type <E.tidarr> tidarr



%%

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


formula_tag :
  |
    { None }
  | OPEN_BRACKET IDENT CLOSE_BRACKET
    { Some (Tag.new_tag (get_name $2)) }


param :
  | VARS
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

(*      decl_global_var v_name s None E.RealVar; *)
      decl_inv_var v_name s None
    }


/***********************    FORMULAS    ************************/



/* FORMULAS */

formula :
  | OPEN_PAREN formula CLOSE_PAREN
      { $2 }
  | literal
      { E.Literal $1 }
  | LOGICAL_TRUE
      { E.True }
  | LOGICAL_FALSE
      { E.False }
  | LOGICAL_NOT formula
      { E.Not $2 }
  | formula LOGICAL_AND formula
      { E.And ($1, $3) }
  | formula LOGICAL_OR formula
      { E.Or ($1, $3) }
  | formula LOGICAL_THEN formula
      { E.Implies ($1, $3) }
  | formula EQUALS formula
      { E.Iff ($1, $3) }
  | AT NUMBER opt_th_param DOT
      {
        let line_num = $2 in
        let th_p     = $3 in
          E.pc_form line_num th_p false
      }
  | AT IDENT opt_th_param DOT
      {
        let label_name = get_name $2 in
        let th_p       = $3 in
        let labelTbl   = System.get_labels !Symtbl.sys in
        let pc_pos     = System.get_label_pos labelTbl label_name in
(*      let pos_list = List.map (fun p -> E.pc_form p th_p false) pc_list *)
        let pc_expr    = match pc_pos with
                           None -> parser_error ("Unknown label: " ^ label_name)
                         | Some (i,e) -> if i = e then
                                           E.PC (i, th_p, false)
                                         else
                                           E.PCRange (i, e, th_p, false)
        in
          E.Literal (E.Atom pc_expr)
(*          E.disj_list pos_list *)
      }


/* THREAD VARSS */


opt_th_param:
  |
    { E.Shared }
  | th_param
    { $1 }


th_param:
  | OPEN_PAREN IDENT CLOSE_PAREN
    {
      let th_id = get_name $2 in
        E.Local (E.build_var_tid th_id)
    }
  | OPEN_PAREN NUMBER CLOSE_PAREN
    {
      let th_id = $2 in
        E.Local (E.build_num_tid th_id)
    }



/* LITERALS */

literal :
  | APPEND OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "append(%s,%s,%s)" (E.term_to_str $3)
                                                       (E.term_to_str $5)
                                                       (E.term_to_str $7) in
      let p1   = parser_check_type check_type_path $3 E.Path get_str_expr in
      let p2   = parser_check_type check_type_path $5 E.Path get_str_expr in
      let pres = parser_check_type check_type_path $7 E.Path get_str_expr in
        E.Atom (E.Append (p1,p2,pres))
    }
  | REACH OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "reach(%s,%s,%s,%s)" (E.term_to_str $3)
                                                         (E.term_to_str $5)
                                                         (E.term_to_str $7)
                                                         (E.term_to_str $9) in
      let h      = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 E.Addr get_str_expr in
      let p      = parser_check_type check_type_path $9 E.Path get_str_expr in
        E.Atom (E.Reach (h,a_from,a_to,p))
    }
  | REACH OPEN_PAREN term COMMA term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "reach(%s,%s,%s,%s,%s)" (E.term_to_str $3)
                                                            (E.term_to_str $5)
                                                            (E.term_to_str $7)
                                                            (E.term_to_str $9)
                                                            (E.term_to_str $11) in
      let h      = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 E.Addr get_str_expr in
      let p      = parser_check_type check_type_path $9 E.Path get_str_expr in
      let l      = parser_check_type check_type_int $11 E.Int get_str_expr in
        E.Atom (E.ReachAt (h,a_from,a_to,l,p))
    }
  | ORDERLIST OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "orderlist(%s,%s,%s)" (E.term_to_str $3)
                                                          (E.term_to_str $5)
                                                          (E.term_to_str $7) in
      let h      = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a_from = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $7 E.Addr get_str_expr in
        E.Atom (E.OrderList (h,a_from,a_to))
    }
  | SKIPLIST OPEN_PAREN term COMMA term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "skiplist(%s,%s,%s,%s,%s)"
                                        (E.term_to_str $3)
                                        (E.term_to_str $5)
                                        (E.term_to_str $7)
                                        (E.term_to_str $9)
                                        (E.term_to_str $11) in
      let h      = parser_check_type check_type_mem  $3  E.Mem get_str_expr in
      let s      = parser_check_type check_type_set  $5  E.Set get_str_expr in
      let l      = parser_check_type check_type_int  $7  E.Int get_str_expr in
      let a_from = parser_check_type check_type_addr $9  E.Addr get_str_expr in
      let a_to   = parser_check_type check_type_addr $11 E.Addr get_str_expr in
        E.Atom (E.Skiplist (h,s,l,a_from,a_to))
    }
  | term IN term
    {
      let get_str_expr () = sprintf "%s in %s" (E.term_to_str $1)
                                               (E.term_to_str $3) in
      let a = parser_check_type check_type_addr $1 E.Addr get_str_expr in
      let r = parser_check_type check_type_set  $3 E.Set get_str_expr in
        E.Atom (E.In (a,r))
    }
  | term SUBSETEQ term
    {
      let get_str_expr () = sprintf "%s subseteq %s)" (E.term_to_str $1)
                                                      (E.term_to_str $3) in
      let s = parser_check_type check_type_set  $1 E.Set get_str_expr in
      let r = parser_check_type check_type_set  $3 E.Set get_str_expr in
        E.Atom (E.SubsetEq(s,r))
    }
  | term INTH term
    {
      let get_str_expr () = sprintf "%s inTh %s" (E.term_to_str $1)
                                                 (E.term_to_str $3) in
      let th = parser_check_type check_type_thid  $1 E.Tid get_str_expr in
      let s  = parser_check_type check_type_setth $3 E.SetTh get_str_expr in
        E.Atom (E.InTh (th,s))
    }
  | term SUBSETEQTH term
    {
      let get_str_expr () = sprintf "%s subseteqTh %s" (E.term_to_str $1)
                                                       (E.term_to_str $3) in
      let r = parser_check_type check_type_setth $1 E.SetTh get_str_expr in
      let s = parser_check_type check_type_setth $3 E.SetTh get_str_expr in
        E.Atom (E.SubsetEqTh(r,s))
    }
  | term ININT term
    {
      let get_str_expr () = sprintf "%s inInt %s" (E.term_to_str $1)
                                                  (E.term_to_str $3) in
      let i = parser_check_type check_type_int $1 E.Int get_str_expr in
      let s = parser_check_type check_type_setint $3 E.SetInt get_str_expr in
        E.Atom (E.InInt (i,s))
    }
  | term SUBSETEQINT term
    {
      let get_str_expr () = sprintf "%s subseteqInt %s" (E.term_to_str $1)
                                                        (E.term_to_str $3) in
      let r = parser_check_type check_type_setint $1 E.SetInt get_str_expr in
      let s = parser_check_type check_type_setint $3 E.SetInt get_str_expr in
        E.Atom (E.SubsetEqInt(r,s))
    }
  | term INELEM term
    {
      let get_str_expr () = sprintf "%s inElem %s" (E.term_to_str $1)
                                                   (E.term_to_str $3) in
      let e = parser_check_type check_type_elem $1 E.Elem get_str_expr in
      let s = parser_check_type check_type_setelem $3 E.SetElem get_str_expr in
        E.Atom (E.InElem (e,s))
    }
  | term SUBSETEQELEM term
    {
      let get_str_expr () = sprintf "%s subseteqElem %s" (E.term_to_str $1)
                                                         (E.term_to_str $3) in
      let r = parser_check_type check_type_setelem $1 E.SetElem get_str_expr in
      let s = parser_check_type check_type_setelem $3 E.SetElem get_str_expr in
        E.Atom (E.SubsetEqElem(r,s))
    }
  | term MATH_LESS term
    {
      let get_str_expr () = sprintf "%s < %s" (E.term_to_str $1)
                                              (E.term_to_str $3) in
      try
        let e1 = parser_check_type check_type_elem $1 E.Elem get_str_expr in
        let e2 = parser_check_type check_type_elem $3 E.Elem get_str_expr in
          E.Atom (E.LessElem (e1, e2))
      with
        _ -> let i1 = parser_check_type check_type_int $1 E.Int get_str_expr in
             let i2 = parser_check_type check_type_int $3 E.Int get_str_expr in
               E.Atom (E.Less (i1, i2))
    }
  | term MATH_GREATER term
    {
      let get_str_expr () = sprintf "%s > %s" (E.term_to_str $1)
                                              (E.term_to_str $3) in
      try
        let e1 = parser_check_type check_type_elem $1 E.Elem get_str_expr in
        let e2 = parser_check_type check_type_elem $3 E.Elem get_str_expr in
          E.Atom (E.GreaterElem (e1, e2))
      with _ -> let i1 = parser_check_type check_type_int $1 E.Int get_str_expr in
                let i2 = parser_check_type check_type_int $3 E.Int get_str_expr in
                  E.Atom (E.Greater (i1, i2))
    }
  | term MATH_LESS_EQ term
    {
      let get_str_expr () = sprintf "%s <= %s" (E.term_to_str $1)
                                               (E.term_to_str $3) in
      let i1 = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2 = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.Atom (E.LessEq (i1, i2))
    }
  | term MATH_GREATER_EQ term
    {
      let get_str_expr () = sprintf "%s >= %s" (E.term_to_str $1)
                                               (E.term_to_str $3) in
      let i1 = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2 = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.Atom (E.GreaterEq (i1, i2))
    }
  | equals
    { E.Atom (E.Eq($1)) }
  | disequals
    { E.Atom (E.InEq($1)) }
  | DOT ident DOT
    {
      match $2 with
      | E.VarT v -> E.Atom(E.BoolVar v)
      | _           -> raise(Boolean_var_expected $2)
    }



/* EQUALS */

equals :
  | term EQUALS term
    {
      let get_str_expr () = sprintf "%s = %s" (E.term_to_str $1)
                                              (E.term_to_str $3) in
      let t1 = $1 in
      let t2 = $3 in

      parser_check_compatibility t1 t2 get_str_expr ;
      (inject_sort t1, inject_sort t2)
    }


/* DISEQUALS */

disequals :
  | term NOT_EQUALS term
    {
      let get_str_expr () = sprintf "%s != %s" (E.term_to_str $1)
                                               (E.term_to_str $3) in
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
    { E.SetT($1) }
  | elem
    { E.ElemT($1) }
  | thid
    { E.TidT($1) }
  | addr
    { E.AddrT($1) }
  | cell
    { E.CellT($1) }
  | setth
    { E.SetThT($1) }
  | setint
    { E.SetIntT($1) }
  | setelem
    { E.SetElemT($1) }
  | path
    { E.PathT($1) }
  | mem
    { E.MemT($1) }
  | integer
    { E.IntT($1) }
  | arrays
    { $1 }
  | addrarr
    { E.AddrArrayT($1) }
  | tidarr
    { E.TidArrayT($1) }
  | OPEN_PAREN term CLOSE_PAREN
    { $2 }



/* IDENT */

ident :
  IDENT
    {
      define_ident E.GlobalScope (get_name $1) E.Shared
(*
      let id  = get_name $1 in
      let var = E.build_var id E.Unknown false None None E.RealVar in
        inject_sort (E.VarT var)
*)
    }
  | IDENT DOUBLECOLON IDENT
    {
      define_ident (E.Scope (get_name $1)) (get_name $3) E.Shared
(*
      let proc_name = get_name $1 in

      let id            = get_name $3 in
      let _             = check_is_procedure proc_name in
      let _             = check_var_belongs_to_procedure id proc_name in

      let proc_info     = System.get_proc_by_name !Symtbl.sys proc_name in
      let iVars         = System.proc_info_get_input proc_info in
      let lVars         = System.proc_info_get_local proc_info in

      let k             = if System.mem_var iVars id then
                            System.find_var_kind iVars id
                          else
                            System.find_var_kind lVars id in
      let var           = inject_sort (E.VarT
                            (E.build_var id E.Unknown false None
                                            (Some proc_name) k))
      in
        var
*)
    }
  | IDENT DOUBLECOLON IDENT th_param
    {
      define_ident (E.Scope (get_name $1)) (get_name $3) $4
(*
      let proc_name = get_name $1 in
*)
(* Under testing. Possible correction. *)
(*
      let c_proc = if !current_proc <> "" then
                     Some !current_proc
                   else
                     None in
*)
(*
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
      let var           = inject_sort (E.VarT
                            (E.build_var id E.Unknown false th
                                            (Some proc_name) k))
      in
        var
*)
    }


/* SET terms*/

set :
  | EMPTYSET
    { E.EmptySet }
  | OPEN_SET term CLOSE_SET
    {
      let get_str_expr() = sprintf "{ %s }" (E.term_to_str $2) in
      let a = parser_check_type check_type_addr $2 E.Addr get_str_expr in
        E.Singl(a)
    }
  | UNION OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "Union(%s,%s)" (E.term_to_str $3)
                                                  (E.term_to_str $5) in
      let s1 = parser_check_type check_type_set  $3 E.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $5 E.Set get_str_expr in
        E.Union(s1,s2)
    }
  | INTR OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "Intr(%s,%s)" (E.term_to_str $3)
                                                 (E.term_to_str $5) in
      let s1 = parser_check_type check_type_set  $3 E.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $5 E.Set get_str_expr in
        E.Intr(s1,s2)
    }
  | SETDIFF OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiff(%s,%s)" (E.term_to_str $3)
                                                    (E.term_to_str $5) in
      let s1 = parser_check_type check_type_set  $3 E.Set get_str_expr in
      let s2 = parser_check_type check_type_set  $5 E.Set get_str_expr in
        E.Setdiff(s1,s2)
    }
  | PATH2SET OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "path2set(%s)" (E.term_to_str $3) in
      let p = parser_check_type check_type_path $3 E.Path get_str_expr in
        E.PathToSet(p)
    }
  | ADDR2SET OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "addr2set(%s,%s)" (E.term_to_str $3)
                                                      (E.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 E.Addr get_str_expr in
        E.AddrToSet(h,a)
    }
  | ADDR2SET OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "addr2set(%s,%s,%s)" (E.term_to_str $3)
                                                         (E.term_to_str $5)
                                                         (E.term_to_str $7) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let l = parser_check_type check_type_int $7 E.Int get_str_expr in
        E.AddrToSetAt(h,a,l)
    }


/* ELEM terms */

elem :
  | term DOT DATA
    {
      let get_str_expr () = sprintf "%s.data" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 E.Cell get_str_expr in
        E.CellData(c)
    }
  | LOWEST_ELEM
    {
      E.LowestElem
    }
  | HIGHEST_ELEM
    {
      E.HighestElem
    }


/* THID terms */

thid :
  | term DOT LOCKID
    {
      let get_str_expr () = sprintf "%s.lockid" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 E.Cell get_str_expr in
        E.CellLockId(c)
    }
  | SHARP
    { E.NoTid }


/* ADDR terms */

addr :
  | NULL
    { E.Null }
  | term DOT NEXT
    {
      let get_str_expr () = sprintf "%s.next" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell  $1 E.Cell get_str_expr in
        E.Next(c)
    }
  | term DOT NEXTAT OPEN_BRACKET term CLOSE_BRACKET
    {
      let get_str_expr () = sprintf "%s.nextat[%s]" (E.term_to_str $1)
                                                    (E.term_to_str $5) in
      let c = parser_check_type check_type_cell  $1 E.Cell get_str_expr in
      let l = parser_check_type check_type_int   $5 E.Cell get_str_expr in
        E.NextAt(c,l)
    }

  | FIRSTLOCKED OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "firstlocked(%s,%s)" (E.term_to_str $3)
                                                         (E.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let p = parser_check_type check_type_path $5 E.Path get_str_expr in
        E.FirstLocked(h,p)
    }
  | FIRSTLOCKED OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "firstlocked(%s,%s,%s)"
                                          (E.term_to_str $3)
                                          (E.term_to_str $5)
                                          (E.term_to_str $7) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let p = parser_check_type check_type_path $5 E.Path get_str_expr in
      let l = parser_check_type check_type_int $7 E.Int get_str_expr in
        E.FirstLockedAt(h,p,l)
    }

/* CELL terms */

cell :
  | ERROR
    { E.Error }
  | MKCELL OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "mkcell(%s,%s,%s)"
                                           (E.term_to_str $3)
                                           (E.term_to_str $5)
                                           (E.term_to_str $7) in
      let d  = parser_check_type check_type_elem $3 E.Elem get_str_expr in
      let a  = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let th = parser_check_type check_type_thid $7 E.Tid get_str_expr in
        E.MkCell(d,a,th)
    }
  | MKCELL OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "mkcell(%s,%s,%s,%s)"
                                           (E.term_to_str $3)
                                           (E.term_to_str $5)
                                           (E.term_to_str $7)
                                           (E.term_to_str $9) in
      let e  = parser_check_type check_type_elem $3 E.Elem get_str_expr in
      let aa = parser_check_type check_type_addrarr $5 E.AddrArray get_str_expr in
      let ta = parser_check_type check_type_tidarr $7 E.TidArray get_str_expr in
      let l  = parser_check_type check_type_int $9 E.Int get_str_expr in
        E.MkSLCell(e,aa,ta,l)
    }
  | MKCELL OPEN_PAREN term COMMA
                      OPEN_BRACKET term_list CLOSE_BRACKET COMMA
                      OPEN_BRACKET term_list CLOSE_BRACKET CLOSE_PAREN
    {
      let list_term_to_str ts = String.concat "," (List.map E.term_to_str ts) in
      let addrs_str = list_term_to_str $6 in
      let tids_str = list_term_to_str $10 in
      let get_str_expr () = sprintf "mkcell(%s,[%s],[%s])"
                                           (E.term_to_str $3)
                                           (addrs_str)
                                           (tids_str) in
      let e  = parser_check_type check_type_elem $3 E.Elem get_str_expr in
      let addrs = List.map (fun a ->
                    parser_check_type check_type_addr a E.Addr get_str_expr
                  ) $6 in
      let tids = List.map (fun t ->
                   parser_check_type check_type_thid t E.Tid get_str_expr
                 ) $10 in
      if List.length addrs <> List.length tids then
        begin
          Interface.Err.msg "Different argument lengths" $
            sprintf "mkcell is invoked with an unequal number of addresses [%s] \
                     and thread ids [%s]." addrs_str tids_str;
          raise(Different_argument_length(addrs_str,tids_str))
        end
      else
        E.MkSLKCell(e,addrs,tids)
    }
  | term DOT LOCK OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "%s.lock(%s)" (E.term_to_str $1)
                                                  (E.term_to_str $5) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
      let t = parser_check_type check_type_thid $5 E.Tid get_str_expr in
        E.CellLock(c,t)
    }
  | term DOT LOCKAT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "%s.lock(%s)" (E.term_to_str $1)
                                                  (E.term_to_str $5) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
      let l = parser_check_type check_type_int  $5 E.Int get_str_expr in
      let t = parser_check_type check_type_thid $7 E.Tid get_str_expr in
        E.CellLockAt(c,l,t)
    }
  | term DOT UNLOCK
    {
      let get_str_expr () = sprintf "%s.unlock" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
        E.CellUnlock(c)
    }
  | term DOT UNLOCKAT OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "%s.unlock" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
      let l = parser_check_type check_type_int  $5 E.Int get_str_expr in
        E.CellUnlockAt(c,l)
    }
  | MEMORY_READ OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "%s [ %s ]" (E.term_to_str $3)
                                                (E.term_to_str $5) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 E.Addr get_str_expr in
        E.CellAt(h,a)
    }


term_list :
  | term COMMA term
    { [$1;$3] }
  | term COMMA term_list
    { $1 :: $3 }



/* SETTH terms*/

setth :
  | EMPTYSETTH
  { E.EmptySetTh }
  | SINGLETH OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleTh(%s)" (E.term_to_str $3) in
      let th = parser_check_type check_type_thid  $3 E.Tid get_str_expr in
        E.SinglTh(th)
    }
  | UNIONTH OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "UnionTh(%s,%s)" (E.term_to_str $3)
                                                    (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setth  $3 E.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $5 E.SetTh get_str_expr in
        E.UnionTh(s1,s2)
    }
  | INTRTH OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "IntrTh(%s,%s)" (E.term_to_str $3)
                                                   (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setth  $3 E.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $5 E.SetTh get_str_expr in
        E.IntrTh(s1,s2)
    }
  | SETDIFFTH OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiffTh(%s,%s)" (E.term_to_str $3)
                                                      (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setth  $3 E.SetTh get_str_expr in
      let s2 = parser_check_type check_type_setth  $5 E.SetTh get_str_expr in
        E.SetdiffTh(s1,s2)
    }


/* SETINT terms*/
setint :
  | EMPTYSETINT
     { E.EmptySetInt }
  | SINGLEINT OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleInt(%s)" (E.term_to_str $3) in
      let th = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.SinglInt(th)
    }
  | UNIONINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "UnionInt(%s,%s)" (E.term_to_str $3)
                                                     (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setint  $3 E.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint  $5 E.SetInt get_str_expr in
        E.UnionInt(s1,s2)
    }
  | INTRINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "IntrInt(%s,%s)" (E.term_to_str $3)
                                                    (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setint  $3 E.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint  $5 E.SetInt get_str_expr in
        E.IntrInt(s1,s2)
    }
  | SETDIFFINT OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiffInt(%s,%s)" (E.term_to_str $3)
                                                       (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setint $3 E.SetInt get_str_expr in
      let s2 = parser_check_type check_type_setint $5 E.SetInt get_str_expr in
        E.SetdiffInt(s1,s2)
    }


/* SETELEM terms*/
setelem :
  | EMPTYSETELEM
     { E.EmptySetElem }
  | SINGLEELEM OPEN_PAREN term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SingleElem(%s)" (E.term_to_str $3) in
      let e = parser_check_type check_type_elem $3 E.Elem get_str_expr in
        E.SinglElem(e)
    }
  | UNIONELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "UnionElem(%s,%s)" (E.term_to_str $3)
                                                      (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 E.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 E.SetElem get_str_expr in
        E.UnionElem(s1,s2)
    }
  | INTRELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "IntrElem(%s,%s)" (E.term_to_str $3)
                                                     (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 E.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 E.SetElem get_str_expr in
        E.IntrElem(s1,s2)
    }
  | SETDIFFELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr() = sprintf "SetDiffElem(%s,%s)" (E.term_to_str $3)
                                                        (E.term_to_str $5) in
      let s1 = parser_check_type check_type_setelem $3 E.SetElem get_str_expr in
      let s2 = parser_check_type check_type_setelem $5 E.SetElem get_str_expr in
        E.SetdiffElem(s1,s2)
    }
  | SET2ELEM OPEN_PAREN term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "set2elem(%s,%s)" (E.term_to_str $3)
                                                      (E.term_to_str $5) in
      let m = parser_check_type check_type_mem $3 E.Mem get_str_expr in
      let s = parser_check_type check_type_set $5 E.Set get_str_expr in
        E.SetToElems(s,m)
    }


/* PATH terms */

path :
  | EPSILON
    { E.Epsilon }
  | OPEN_BRACKET term CLOSE_BRACKET
    {
      let get_str_expr () = sprintf "[ %s ]" (E.term_to_str $2) in
      let a = parser_check_type check_type_addr $2 E.Addr get_str_expr in
        E.SimplePath(a)
    }
  | GETP OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "getp(%s,%s,%s)" (E.term_to_str $3)
                                                     (E.term_to_str $5)
                                                     (E.term_to_str $7) in
      let h     = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let first = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let last  = parser_check_type check_type_addr $7 E.Addr get_str_expr in
        E.GetPath(h,first,last)
    }
  | GETP OPEN_PAREN term COMMA term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "getp(%s,%s,%s,%s)" (E.term_to_str $3)
                                                        (E.term_to_str $5)
                                                        (E.term_to_str $7)
                                                        (E.term_to_str $9) in
      let h     = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let first = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let last  = parser_check_type check_type_addr $7 E.Addr get_str_expr in
      let l     = parser_check_type check_type_int $9 E.Int get_str_expr in
        E.GetPathAt(h,first,last,l)
  }


/* MEM terms */

mem :
  | UPDATE OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "update(%s,%s,%s)" (E.term_to_str $3)
                                                       (E.term_to_str $5)
                                                       (E.term_to_str $7) in
      let h = parser_check_type check_type_mem  $3 E.Mem get_str_expr in
      let a = parser_check_type check_type_addr $5 E.Addr get_str_expr in
      let c = parser_check_type check_type_cell $7 E.Cell get_str_expr in
        E.Update(h,a,c)
    }


/* INTEGER terms*/

integer :
  | NUMBER
    { E.IntVal $1 }
  | MATH_MINUS term %prec MATH_NEG
    {
      let get_str_expr () = sprintf "-%s" (E.term_to_str $2) in
      let i  = parser_check_type check_type_int $2 E.Int get_str_expr in
        E.IntNeg i
    }
  | term MATH_PLUS term
    {
      let get_str_expr () = sprintf "%s+%s" (E.term_to_str $1)
                                            (E.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.IntAdd (i1,i2)
    }
  | term MATH_MINUS term
    {
      let get_str_expr () = sprintf "%s-%s" (E.term_to_str $1)
                                            (E.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.IntSub (i1,i2)
    }
  | term MATH_MULT term
    {
      let get_str_expr () = sprintf "%s*%s" (E.term_to_str $1)
                                            (E.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.IntMul (i1,i2)
    }
  | term MATH_DIV term
    {
      let get_str_expr () = sprintf "%s/%s" (E.term_to_str $1)
                                            (E.term_to_str $3) in
      let i1  = parser_check_type check_type_int $1 E.Int get_str_expr in
      let i2  = parser_check_type check_type_int $3 E.Int get_str_expr in
        E.IntDiv (i1,i2)
    }
  | SETINTMIN OPEN_PAREN term CLOSE_PAREN
    {
      let iSet = $3 in
      let get_str_expr () = sprintf "setIntMin(%s)" (E.term_to_str iSet) in
      let s  = parser_check_type check_type_setint iSet E.SetInt get_str_expr
      in
        E.IntSetMin (s)
    }
  | SETINTMAX OPEN_PAREN term CLOSE_PAREN
    {
      let iSet = $3 in
      let get_str_expr () = sprintf "setIntMax(%s)" (E.term_to_str iSet) in
      let s  = parser_check_type check_type_setint iSet E.SetInt get_str_expr
      in
        E.IntSetMax (s)
    }
  | term DOT MAX
    {
      let get_str_expr () = sprintf "%s.max" (E.term_to_str $1) in
      let c  = parser_check_type check_type_cell $1 E.Cell get_str_expr
      in
        E.CellMax (c)
    }



/* ARRAY terms */
arrays :
  | term OPEN_BRACKET term CLOSE_BRACKET
    {
      let get_str_expr () = sprintf "%s[%s]" (E.term_to_str $1)
                                             (E.term_to_str $3) in
      let i = parser_check_type check_type_int $3 E.Int get_str_expr in
      try
        let at = parser_check_type check_type_tidarr $1 E.TidArray get_str_expr in
          E.TidT (E.TidArrRd (at,i))
      with _ -> try
        let aa = parser_check_type check_type_addrarr $1 E.AddrArray get_str_expr in
          E.AddrT (E.AddrArrRd (aa,i))
      with e -> try
        let t = parser_check_type check_type_thid $1 E.Tid get_str_expr in
        match t with
        | E.CellLockId c -> E.TidT (E.CellLockIdAt (c,i))
        | _                 -> raise(e)
      with e ->
        let a = parser_check_type check_type_addr $1 E.Addr get_str_expr in
        match a with
        | E.Next c -> E.AddrT (E.ArrAt (c,i))
        | _           -> raise(e)
    }
  | ARR_UPDATE OPEN_PAREN term COMMA term COMMA term CLOSE_PAREN
    {
      let get_str_expr () = sprintf "arrUpd (%s,%s,%s)" (E.term_to_str $3)
                                                        (E.term_to_str $5)
                                                        (E.term_to_str $7) in
      let i = parser_check_type check_type_int $5 E.Int get_str_expr in
      try
        let at = parser_check_type check_type_tidarr $3 E.TidArray get_str_expr in
        let t = parser_check_type check_type_thid $7 E.Tid get_str_expr in
          E.TidArrayT (E.TidArrayUp (at,i,t))
      with _ ->
        let aa = parser_check_type check_type_addrarr $3 E.AddrArray get_str_expr in
        let a = parser_check_type check_type_addr $7 E.Addr get_str_expr in
          E.AddrArrayT (E.AddrArrayUp (aa,i,a))
    }


/* ADDRARR term */
addrarr :
  | term DOT ARR
    {
      let get_str_expr () = sprintf "%s.arr" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
        E.CellArr(c)
    }


/* TIDARR term */
tidarr :
  | term DOT TIDS
    {
      let get_str_expr () = sprintf "%s.tids" (E.term_to_str $1) in
      let c = parser_check_type check_type_cell $1 E.Cell get_str_expr in
        E.CellTids(c)
    }

/************************   TEMPORARY VERIFICATION CONDITIONS **********************/


vc_info :
  | param COLON inv_var_declarations
    SUPPORT COLON formula_list
    TID_CONSTRAINT COLON formula
    RHO COLON formula
    GOAL COLON formula
    TRANSITION_TID COLON term
    LINE COLON NUMBER
      {
        let _ = System.clear_table invVars in
        let supp_list = $6 in
        let tid_phi = $9 in
        let rho_phi = $12 in
        let goal_phi = $15 in
        let trans_tid = parser_check_type check_type_thid $18 E.Tid (fun _ -> (E.term_to_str $18)) in
        let line = $21 in
        let vocab = E.voc (E.conj_list [tid_phi;rho_phi;goal_phi]) in
        Tactics.create_vc_info supp_list tid_phi rho_phi goal_phi vocab trans_tid line
      }

formula_list :
  |
    { [] }
  | formula formula_list
    { $1 :: $2 }
