open TllQuery
open LeapVerbose


module SMTTllQuery : TLL_QUERY =
struct

  module Expr     = TllExpression
  module V        = TllExpression.V
  module VarSet   = V.VarSet
  module VarIdSet = V.VarIdSet
  module B        = Buffer
  module GM       = GenericModel
  module F        = Formula
  module MS       = ModelSize

  exception UnexpectedCellTerm of string

  let prog_lines = ref 0


  let pc_prime_name  : string = Conf.pc_name ^ "_prime"
  let loc_str        : string = "loc_"
  let range_addr_str : string = "rg_addr_"
  let range_tid_str  : string = "rg_tid_"
  let path_len_str   : string = "p_len_"


  let addr_prefix = "aa_"
  let tid_prefix = "tt_"
  let elem_prefix = "ee_"


  (* Sort names *)
  let bool_s    : string = "Bool"
  let int_s     : string = "Int"
  let addr_s    : string = "Address"
  let set_s     : string = "Set"
  let elem_s    : string = "Elem"
  let tid_s     : string = "Tid"
  let cell_s    : string = "Cell"
  let setth_s   : string = "Setth"
  let setelem_s : string = "SetElem"
  let path_s    : string = "Path"
  let heap_s    : string = "Heap"
  let int_s     : string = "Int"
  let unk_s     : string = "Unknown"
  let loc_s     : string = "Loc"


  (* Lock-Unlock information table *)
  (* We store calls to cell_lock and cell_unlock in the formula, in order to
     add the necessary assertions once we have translated the formula *)
  let cell_tbl = Hashtbl.create 10
  let addr_tbl = Hashtbl.create 10
  let elem_tbl = Hashtbl.create 10
  let tid_tbl = Hashtbl.create 10
  let getp_tbl = Hashtbl.create 10
  let locked_tbl = Hashtbl.create 10


  let clean_lists () :  unit =
    Hashtbl.clear cell_tbl;
    Hashtbl.clear addr_tbl;
    Hashtbl.clear elem_tbl;
    Hashtbl.clear tid_tbl;
    Hashtbl.clear getp_tbl;
    Hashtbl.clear locked_tbl


  (* Information storage *)
  let sort_map : GM.sort_map_t = GM.new_sort_map()


  let linenum_to_str (i:int) : string =
    string_of_int i


  let range_addr_to_str (i:int) : string =
    string_of_int i


  let range_tid_to_str (i:int) : string =
    range_tid_str ^ string_of_int i


  let path_len_to_str (i:int) : string =
    string_of_int i


  (* Program lines manipulation *)
  let set_prog_lines (n:int) : unit =
    prog_lines := n



  (************************* Declarations **************************)


  let data(expr:string) : string =
    Hashtbl.add elem_tbl expr ();
    ("(data " ^expr^ ")")


  let next(expr:string) : string =
    Hashtbl.add addr_tbl expr ();
    ("(next " ^expr^ ")")


  let lock(expr:string) : string =
    Hashtbl.add tid_tbl expr ();
    ("(lock " ^expr^ ")")


  let smt_addr_preamble (buf:B.t) (num_addr:int) : unit =
    B.add_string buf ("(set-logic QF_AUFLIA)\n");
    B.add_string buf ("(define-sort " ^addr_s^ " () " ^int_s^ ")\n");
    GM.sm_decl_const sort_map "max_address" int_s ;
    B.add_string buf
      ( "(define-fun max_address () " ^int_s^ " " ^(string_of_int num_addr)^ ")\n");
    B.add_string buf
      ("(define-fun null () " ^addr_s^ " 0)\n");
    for i = 1 to num_addr do
      let i_str = string_of_int i in
      let a_str = addr_prefix ^ i_str in
      B.add_string buf ("(define-fun " ^a_str^ " () " ^addr_s^ " " ^i_str^ ")\n")
    done;
    B.add_string buf ("(define-fun isaddr ((x " ^addr_s^ ")) " ^bool_s^ " (and (<= 0 x) (<= x max_address)))\n");
    B.add_string buf
      ( "(define-sort RangeAddress () " ^int_s^ ")\n" ^
        "(define-fun is_valid_range_address ((i RangeAddress)) " ^bool_s^
            " (and (<= 0 i) (<= i max_address)))\n")


  let smt_tid_preamble (buf:B.t) (num_tids:int) : unit =
    B.add_string buf ("(define-sort " ^tid_s^ " () " ^int_s^ ")\n");
    GM.sm_decl_const sort_map "max_tid" int_s ;
    B.add_string buf ("(define-fun max_tid () " ^int_s^ " " ^(string_of_int num_tids)^ ")\n");
    B.add_string buf
      ("(define-fun notid () " ^tid_s^ " 0)\n");
    for i = 1 to num_tids do
      let i_str = string_of_int i in
      let t_str = tid_prefix ^ i_str in
      B.add_string buf ("(define-fun " ^t_str^ " () " ^tid_s^ " " ^i_str^ ")\n")
    done;
    B.add_string buf "; I need the line below to prevent an unknown constant error\n";
    GM.sm_decl_const sort_map "tid_witness" tid_s ;
    let witness_str = string_of_int (num_tids + 1) in
    B.add_string buf ("(define-fun tid_witness () " ^tid_s^ " " ^witness_str^ ")\n");
    B.add_string buf ("(define-fun istid ((x " ^tid_s^ ")) " ^bool_s^ " (and (<= 0 x) (<= x (+ max_tid 1))))\n")


  (* (define-type element) *)
  let smt_element_preamble (buf:B.t) (num_elems:int) : unit =
    B.add_string buf ("(define-sort " ^elem_s^ " () " ^int_s^ ")\n");
    B.add_string buf ("(define-fun lowestElem () " ^elem_s^ " 0)\n");
    B.add_string buf ("(define-fun highestElem () " ^elem_s^ " " ^(string_of_int (num_elems+1))^ ")\n");
    for i = 1 to num_elems do
      let i_str = string_of_int i in
      let e_str = elem_prefix ^ i_str in
      B.add_string buf ("(define-fun " ^e_str^ " () " ^elem_s^ " " ^i_str^ ")\n")
    done;
    B.add_string buf ("(define-fun iselem ((x " ^elem_s^ ")) " ^bool_s^ " (and (<= lowestElem x) (<= x highestElem)))\n")



  let smt_cell_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(declare-sort " ^cell_s^ " 0)\n\
        (declare-fun mkcell (" ^elem_s^ " " ^addr_s^ " " ^tid_s^ ") " ^cell_s^ ")\n\
        (declare-fun data (" ^cell_s^ ") " ^elem_s^ ")\n\
        (declare-fun next (" ^cell_s^ ") " ^addr_s^ ")\n\
        (declare-fun lock (" ^cell_s^ ") " ^tid_s^ ")\n")


  let smt_heap_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(define-sort " ^heap_s^ " () (Array " ^addr_s^ " " ^cell_s^ "))\n")


  let smt_set_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(define-sort " ^set_s^ " () (Array " ^addr_s^ " " ^bool_s^ "))\n")


  let smt_setth_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(define-sort " ^setth_s^ " () (Array " ^tid_s^ " " ^bool_s^ "))\n")


  let smt_setelem_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(define-sort " ^setelem_s^ " () (Array " ^elem_s^ " " ^bool_s^ "))\n")


  let smt_path_preamble (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ( "(define-sort PathLength () " ^int_s^ ")\n" ^
        "(define-fun is_valid_path_length ((i PathLength)) " ^bool_s^
            " (and (<= 0 i) (<= i (+ max_address 1))))\n");
    B.add_string buf
      ( "(define-sort PathAt () (Array RangeAddress " ^addr_s^ "))\n" ^
        "(define-sort PathWhere () (Array " ^addr_s^ " RangeAddress))\n");
    B.add_string buf
      ( "(declare-sort " ^path_s^ " 0)\n" );
    B.add_string buf
      ( "(declare-fun mkpath (PathLength PathAt PathWhere " ^set_s^ ") " ^path_s^ ")\n" );
    B.add_string buf
      ( "(declare-fun length (" ^path_s^ ") PathLength)\n\
         (declare-fun at     (" ^path_s^ ") PathAt)\n\
         (declare-fun where  (" ^path_s^ ") PathWhere)\n\
         (declare-fun addrs  (" ^path_s^ ") " ^set_s^ ")\n" );
    B.add_string buf
      ("(define-fun eqpath_pos ((p " ^path_s^ ") (r " ^path_s^
            ") (i RangeAddress)) " ^bool_s^ "\n" ^
       "  (=> (and (is_valid_range_address i) (< i (length p)) (< i (length r)))\n" ^
       "      (= (select (at p) i) (select (at r) i))))\n");
    B.add_string buf
      ("(define-fun eqpath ((p " ^path_s^ ") (r " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (and (= (length p) (length r))\n");
    for i=0 to num_addr do
      B.add_string buf
        ("     (eqpath_pos p r "^ (path_len_to_str i) ^ ")\n");
    done ;
      B.add_string buf "))\n"


  let smt_unknown_preamble (buf:B.t) : unit =
    B.add_string buf
      ("(declare-sort " ^unk_s^ " 0)\n")


  let smt_pos_preamble (buf:B.t) : unit =
    (* No need to define the program counter as now is just a integer variable *)
    B.add_string buf ("(define-sort " ^loc_s^ " () " ^int_s^ ")\n")
    (* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)
    (*
    GM.sm_decl_fun sort_map Conf.pc_name [tid_s] [loc_s] ;
    GM.sm_decl_fun sort_map pc_prime_name [tid_s] [loc_s] ;
    B.add_string buf ("(declare-fun " ^Conf.pc_name^ " () (Array " ^tid_s^ " " ^loc_s^ "))\n");
    B.add_string buf ("(declare-fun " ^pc_prime_name^ " () (Array " ^tid_s^ " " ^loc_s^ "))\n");
    B.add_string buf ("(define-fun in_pos_range ((t " ^tid_s^ ")) " ^bool_s^ "\n" ^
                      "   (and (<= 1 (select pc t))\n" ^
                      "        (<= (select pc t) " ^string_of_int !prog_lines^ ")\n" ^
                      "        (<= 1 (select pc_prime t))\n" ^
                      "        (<= (select pc_prime t) " ^ string_of_int !prog_lines^ ")))\n")
    *)
    (* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)


  let smt_empth_def (buf:B.t) (num_tids:int) : unit =
    let _ = GM.sm_decl_const sort_map "emptyth" setth_s in
    B.add_string buf
      ("(declare-fun emptyth () " ^setth_s^ ")\n");
    B.add_string buf
      ("(assert (= (select emptyth notid) false))\n");
    for i = 1 to num_tids do
      B.add_string buf
        ("(assert (= (select emptyth " ^(tid_prefix ^ (string_of_int i))^ ") false))\n")
    done;
    B.add_string buf
      ("(assert (= (select emptyth tid_witness) false))\n")


  let smt_singletonth_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun singletonth ((t " ^tid_s^ ")) " ^setth_s^ "\n" ^
       "  (store emptyth t true))\n")


  let smt_unionth_def (buf:B.t) (num_tids:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyth notid (or (select s1 notid) (select s2 notid)))\n" ^
                   "                   tid_witness (or (select s1 tid_witness) (select s2 tid_witness)))") in
    for i = 1 to num_tids do
      let t_str = tid_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                   " ^t_str^ " (or (select s1 " ^t_str^ ") (select s2 " ^t_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun unionth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) " ^setth_s^ "\n" ^ (!str) ^ ")\n")


  let smt_intersectionth_def (buf:B.t) (num_tids:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyth notid (and (select s1 notid) (select s2 notid)))\n" ^
                   "                   tid_witness (and (select s1 tid_witness) (select s2 tid_witness)))") in
    for i = 1 to num_tids do
      let t_str = tid_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                   " ^t_str^ " (and (select s1 " ^t_str^ ") (select s2 " ^t_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun intersectionth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) " ^setth_s^ "\n" ^ (!str) ^ ")\n")


  let smt_setdiffth_def (buf:B.t) (num_tids:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyth notid (and (select s1 notid) (not (select s2 notid))))\n" ^
                   "                   tid_witness (and (select s1 tid_witness) (not (select s2 tid_witness))))") in
    for i = 1 to num_tids do
      let t_str = tid_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                   " ^t_str^ " (and (select s1 " ^t_str^ ") (not (select s2 " ^t_str^ "))))"
    done;
    B.add_string buf
      ("(define-fun setdiffth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) " ^setth_s^ "\n" ^ (!str) ^ ")\n")


  let smt_subseteqth_def (buf:B.t) (num_tids:int) : unit =
    B.add_string buf
      ("(define-fun subseteqth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) "^bool_s^ "\n" ^
       "  (and (=> (select s1 notid) (select s2 notid))\n" ^
       "       (=> (select s1 tid_witness) (select s2 tid_witness))\n");
    for i = 1 to num_tids do
      let t_str = tid_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (=> (select s1 " ^t_str^ ") (select s2 " ^t_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_eqsetth_def (buf:B.t) (num_tids:int) : unit =
    B.add_string buf
      ("(define-fun eqsetth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) "^bool_s^ "\n" ^
       "  (and (= (select s1 notid) (select s2 notid))\n" ^
       "       (= (select s1 tid_witness) (select s2 tid_witness))\n");
    for i = 1 to num_tids do
      let t_str = tid_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (= (select s1 " ^t_str^ ") (select s2 " ^t_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_empelem_def (buf:B.t) (num_elems:int) : unit =
    let _ = GM.sm_decl_const sort_map "emptyelem" setelem_s in
    B.add_string buf
      ("(declare-fun emptyelem () " ^setelem_s^ ")\n");
    B.add_string buf
      ("(assert (= (select emptyelem lowestElem) false))\n");
    B.add_string buf
      ("(assert (= (select emptyelem highestElem) false))\n");
    for i = 1 to num_elems do
      B.add_string buf
        ("(assert (= (select emptyelem " ^(elem_prefix ^ (string_of_int i))^ ") false))\n")
    done


  let smt_singletonelem_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun singletonelem ((e " ^elem_s^ ")) " ^setelem_s^ "\n" ^
       "  (store emptyelem e true))\n")


  let smt_unionelem_def (buf:B.t) (num_elems:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyelem lowestElem (or (select s1 lowestElem) (select s2 lowestElem)))\n" ^
                   "                     highestElem (or (select s1 highestElem) (select s2 highestElem)))") in
    for i = 1 to num_elems do
      let e_str = elem_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                     " ^e_str^ " (or (select s1 " ^e_str^ ") (select s2 " ^e_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun unionelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) " ^setelem_s^ "\n" ^ (!str) ^ ")\n")


  let smt_intersectionelem_def (buf:B.t) (num_elems:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyelem lowestElem (and (select s1 lowestElem) (select s2 lowestElem)))\n" ^
                   "                     highestElem (and (select s1 highestElem) (select s2 highestElem)))") in
    for i = 1 to num_elems do
      let e_str = elem_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                     " ^e_str^ " (and (select s1 " ^e_str^ ") (select s2 " ^e_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun intersectionelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) " ^setelem_s^ "\n" ^ (!str) ^ ")\n")


  let smt_setdiffelem_def (buf:B.t) (num_elems:int) : unit =
    let str = ref ("  (store\n" ^
                   "    (store emptyelem lowestElem (and (select s1 lowestElem) (not (select s2 lowestElem))))\n" ^
                   "                     highestElem (and (select s1 highestElem) (not (select s2 highestElem))))") in
    for i = 1 to num_elems do
      let e_str = elem_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                     " ^e_str^ " (and (select s1 " ^e_str^ ") (not (select s2 " ^e_str^ "))))"
    done;
    B.add_string buf
      ("(define-fun setdiffelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) " ^setelem_s^ "\n" ^ (!str) ^ ")\n")


  let smt_subseteqelem_def (buf:B.t) (num_elem:int) : unit =
    B.add_string buf
      ("(define-fun subseteqelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) "^bool_s^ "\n" ^
       "  (and (=> (select s1 lowestElem) (select s2 lowestElem))\n" ^
       "       (=> (select s1 highestElem) (select s2 highestElem))\n");
    for i = 1 to num_elem do
      let e_str = elem_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (=> (select s1 " ^e_str^ ") (select s2 " ^e_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_eqsetelem_def (buf:B.t) (num_elem:int) : unit =
    B.add_string buf
      ("(define-fun eqsetelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) "^bool_s^ "\n" ^
       "  (and (= (select s1 lowestElem) (select s2 lowestElem))\n" ^
       "       (= (select s1 highestElem) (select s2 highestElem))\n");
    for i = 1 to num_elem do
      let e_str = elem_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (= (select s1 " ^e_str^ ") (select s2 " ^e_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_emp_def (buf:B.t) (num_addrs:int) : unit =
    let _ = GM.sm_decl_const sort_map "empty" set_s in
    B.add_string buf
      ("(declare-fun empty () " ^set_s^ ")\n");
    B.add_string buf
      ("(assert (= (select empty null) false))\n");
    for i = 1 to num_addrs do
      B.add_string buf
        ("(assert (= (select empty " ^(addr_prefix ^ (string_of_int i))^ ") false))\n")
    done


  let smt_singleton_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun singleton ((a " ^addr_s^ ")) " ^set_s^ "\n" ^
       "  (store empty a true))\n")


  let smt_union_def (buf:B.t) (num_addrs:int) : unit =
    let str = ref "    (store empty null (or (select s1 null) (select s2 null)))" in
    for i = 1 to num_addrs do
      let a_str = addr_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                 " ^a_str^ " (or (select s1 " ^a_str^ ") (select s2 " ^a_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun setunion ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^ (!str) ^ ")\n")


  let smt_intersection_def (buf:B.t) (num_addrs:int) : unit =
    let str = ref "    (store empty null (and (select s1 null) (select s2 null)))" in
    for i = 1 to num_addrs do
      let a_str = addr_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                 " ^a_str^ " (and (select s1 " ^a_str^ ") (select s2 " ^a_str^ ")))"
    done;
    B.add_string buf
      ("(define-fun intersection ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^ (!str) ^ ")\n")


  let smt_setdiff_def (buf:B.t) (num_addrs:int) : unit =
    let str = ref "    (store empty null (and (select s1 null) (not (select s2 null))))" in
    for i = 1 to num_addrs do
      let a_str = addr_prefix ^ (string_of_int i) in
      str := "  (store\n" ^ (!str) ^ "\n" ^
             "                 " ^a_str^ " (and (select s1 " ^a_str^ ") (not (select s2 " ^a_str^ "))))"
    done;
    B.add_string buf
      ("(define-fun setdiff ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^set_s^ "\n" ^ (!str) ^ ")\n")


  let smt_subseteq_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun subseteq ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) "^bool_s^ "\n" ^
       "  (and (=> (select s1 null) (select s2 null))\n");
    for i = 1 to num_addr do
      let a_str = addr_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (=> (select s1 " ^a_str^ ") (select s2 " ^a_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_eqset_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun eqset ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) "^bool_s^ "\n" ^
       "  (and (= (select s1 null) (select s2 null))\n");
    for i = 1 to num_addr do
      let a_str = addr_prefix ^ (string_of_int i) in
      B.add_string buf
        ("       (= (select s1 " ^a_str^ ") (select s2 " ^a_str^ "))\n")
    done;
    B.add_string buf ("))\n")


  let smt_settoelems_def (buf:B.t) (num_addrs:int) : unit =
    let str = ref "    (store emptyelem (data (select m null)) (select s null))\n" in
    for i=1 to num_addrs do
      let aa_i = addr_prefix ^ (string_of_int i) in
      str := "  (unionelem\n" ^ !str ^
             "    (store emptyelem (data (select m " ^aa_i^ ")) (select s " ^aa_i^ ")))\n"
    done;
    B.add_string buf
    ("(define-fun set2elem ((s " ^set_s^ ") (m " ^heap_s^ ")) " ^setelem_s^
      "\n" ^ !str ^ ")\n")


  let smt_getlocked_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun getlockat ((h " ^heap_s^ ") (p " ^path_s^
            ") (i RangeAddress)) " ^tid_s^ "\n" ^
       "  (ite (is_valid_range_address i) (lock (select h (select (at p) i))) notid))\n" ^
       "(define-fun getaddrat ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
       "  (ite (is_valid_range_address i) (select (at p) i) null))\n" ^
       "(define-fun islockedpos ((h " ^heap_s^ ") (p " ^path_s^
            ") (i RangeAddress)) " ^bool_s^ "\n" ^
       "  (ite (is_valid_range_address i) (and (< i (length p)) (not (= notid (getlockat h p i)))) false))\n")


  let smt_firstlock_def (buf:B.t) (num_addr:int) : unit =
    let strlast = (string_of_int num_addr) in
    B.add_string buf
      ("(define-fun firstlockfrom" ^ strlast ^ " ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p " ^ strlast ^ ") (getaddrat p " ^ strlast ^ ") null))\n");
    for i=(num_addr-1) downto 1 do
      let stri    = (string_of_int i) in
      let strnext = (string_of_int (i+1)) in
          B.add_string buf
      ("(define-fun firstlockfrom"^ stri ^" ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p "^ stri ^") (getaddrat p "^ stri ^") (firstlockfrom"^ strnext ^" h p)))\n");
    done ;
    B.add_string buf
      ("(define-fun firstlock ((h " ^heap_s^ ") (p " ^path_s^ ") ) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p 0) (getaddrat p 0) (firstlockfrom1 h p)))\n")



  let smt_lastlock_def (buf:B.t) (num_addr:int) : unit =
    let strlast = (string_of_int num_addr) in
    let strprelast = (string_of_int (num_addr - 1)) in
    B.add_string buf
      ("(define-fun lastlockfrom0 ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p 0) (getaddrat p 0) null))\n");
    for i = 1 to (num_addr-1) do
      let stri    = (string_of_int i) in
      let strprev = (string_of_int (i - 1)) in
          B.add_string buf
      ("(define-fun lastlockfrom"^ stri ^" ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p "^ stri ^") (getaddrat p "^ stri ^") (lastlockfrom"^ strprev ^" h p)))\n");
    done ;
    B.add_string buf
      ("(define-fun lastlock ((h " ^heap_s^ ") (p " ^path_s^ ") ) " ^addr_s^ "\n" ^
       "  (ite (islockedpos h p " ^strlast^ ") (getaddrat p " ^strlast^ ") (lastlockfrom" ^strprelast^ " h p)))\n")



  let smt_lockset_def (buf:B.t) (num_addr:int) : unit =
    let strlast = (string_of_int (max num_addr 1)) in
    B.add_string buf
      ("(define-fun lockset" ^ strlast ^ " ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^setth_s^ "\n" ^
       "  (ite (islockedpos h p " ^ strlast ^ ") (singletonth (getlockat h p " ^ strlast ^ ")) emptyth))\n");
    for i=(num_addr-1) downto 1 do
      let stri    = (string_of_int i) in
      let strnext = (string_of_int (i+1)) in
          B.add_string buf
      ("(define-fun lockset"^ stri ^" ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^setth_s^ "\n" ^
       "  (ite (islockedpos h p "^ stri ^") (unionth (singletonth (getlockat h p "^ stri ^")) (lockset"^ strnext ^" h p)) (lockset" ^strnext^ " h p)))\n");
    done ;
    B.add_string buf
      ("(define-fun lockset ((h " ^heap_s^ ") (p " ^path_s^ ") ) " ^setth_s^ "\n" ^
       "  (ite (islockedpos h p 0) (unionth (singletonth (getlockat h p 0)) (lockset1 h p)) (lockset1 h p)))\n")


  let smt_cell_lock (buf:B.t) : unit =
    B.add_string buf
      ("(declare-fun cell_lock (" ^cell_s^ " " ^tid_s^ ") " ^cell_s^ ")\n")


  let smt_cell_unlock_def (buf:B.t) : unit =
    B.add_string buf
      ("(declare-fun cell_unlock (" ^cell_s^ ") " ^cell_s^ ")\n")


  let smt_epsilon_def (buf:B.t) (num_addr:int) : unit =
    let _ = GM.sm_decl_const sort_map "epsilon" path_s in
    let mkpath_str = "mkpath 0 epsilonat epsilonwhere empty" in
      B.add_string buf
        ("(declare-fun epsilonat () PathAt)\n");
      for i = 0 to (num_addr + 1) do
        B.add_string buf
          ("(assert (= (select epsilonat " ^(string_of_int i)^ ") null))\n")
      done;
      B.add_string buf
        ("(declare-fun epsilonwhere () PathWhere)\n" ^
         "(assert (= (select epsilonwhere null) 0))\n");
      for i = 1 to num_addr do
        B.add_string buf
          ("(assert (= (select epsilonwhere " ^(addr_prefix ^ (string_of_int i))^ ") 0))\n")
      done;
      B.add_string buf
        ("(declare-fun epsilon () " ^path_s^ ")\n" ^
         "(assert (= epsilon (" ^mkpath_str^ ")))\n");
      B.add_string buf
        ("(assert (and (= (length (" ^mkpath_str^ ")) 0)\n\
                       (= (at (" ^mkpath_str^ ")) epsilonat)\n\
                       (= (where (" ^mkpath_str^ ")) epsilonwhere)\n\
                       (= (addrs (" ^mkpath_str^ ")) empty)))\n")


  let smt_singletonpath_def (buf:B.t) (num_addr:int) : unit =
    let mkpath_str = "mkpath 1 (singletonat a) (singletonwhere a) (singleton a)" in
    B.add_string buf
      ("(define-fun singletonat ((a " ^addr_s^ ")) PathAt\n" ^
       "  (store epsilonat 0 a))\n" ^
       "(declare-fun singlewhere () PathWhere)\n" ^
       "(assert (= (select singlewhere null) 1))\n");
    for i = 1 to num_addr do
      B.add_string buf
        ("(assert (= (select singlewhere " ^(addr_prefix ^ (string_of_int i))^ ") 1))\n")
    done;
    B.add_string buf
      ("(define-fun singletonwhere ((a " ^addr_s^ ")) PathWhere\n" ^
       "  (store singlewhere a 0))\n" ^
       "(define-fun singlepath ((a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (" ^mkpath_str^ "))\n")
       (*
      B.add_string buf
        ("(assert (and (= (length (" ^mkpath_str^ ")) 1)\n\
                       (= (at (" ^mkpath_str^ ")) (singletonat a))\n\
                       (= (where (" ^mkpath_str^ ")) (singletonwhere a))\n\
                       (= (addrs (" ^mkpath_str^ ")) (singleton a))))\n")
*)


  let smt_ispath_def (buf:B.t) (num_addr:int) : unit =
    let str = ref "empty" in
    for i=0 to num_addr do
      str := "(setunion \n                            " ^
              !str ^ "\n                               (addr_in_path p " ^string_of_int i^ "))"
    done;
    B.add_string buf
      ("(define-fun addr_in_path ((p " ^path_s^ ") (i RangeAddress)) " ^set_s^ "\n" ^
         "  (ite (and (<= 0 i) (< i (length p)))\n" ^
         "       (singleton (select (at p) i))\n" ^
         "       empty))\n");
    B.add_string buf
      ("(define-fun check_position ((p " ^path_s^ ") (i RangeAddress)) " ^bool_s^ "\n" ^
       "  (and (=> (and (is_valid_range_address i)\n" ^
       "                (< i (length p)))\n" ^
       "           (and (= i (select (where p) (select (at p) i)))\n" ^
       "                (isaddr (select (at p) i))\n" ^
       "                (select (addrs p) (select (at p) i))))\n" ^
       "       (=> (not (and (is_valid_range_address i)\n" ^
       "                     (< i (length p))))\n" ^
       "           (not (select (addrs p) (select (at p) i))))))\n");
    B.add_string buf
      ("(define-fun ispath ((p " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (or (eqpath p epsilon)\n" ^
       "    (and (<= (length p) (+ max_address 1))\n");
    for i=0 to num_addr do
      B.add_string buf
        ("\n          (and (check_position p " ^ (string_of_int i) ^ ")\n" ^
         "               (= (addrs p) " ^ !str ^ "))\n")
    done ;
    B.add_string buf ")))\n"


  let smt_rev_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun rev_position ((p " ^path_s^ ") (p_rev " ^path_s^ ") (i RangeAddress)) " ^bool_s^ "\n" ^
       "  (=> (and (is_valid_range_address i)\n" ^
       "           (< i (length p)))\n" ^
       "      (= (select (at p) i) (select (at p_rev) (- (length p) i)))))\n");
    B.add_string buf
      ("(define-fun rev ((p " ^path_s^ ") (p_rev " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (and (= (length p) (length p_rev))");
       for i=0 to num_addr do
         B.add_string buf
      ( "\n     (rev_position p p_rev " ^ (string_of_int i) ^")" )
       done ;
       B.add_string buf "))\n"


  let smt_path2set_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun path2set ((p " ^path_s^ ")) " ^set_s^ " (addrs p))\n")


  let smt_dref_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun deref ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^cell_s^ "\n" ^
       "  (select h a))\n")


  let smt_elemorder_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun lesselem ((x " ^elem_s^ ") (y " ^elem_s^ ")) " ^bool_s^ " (< x y))\n" ^
       "(define-fun greaterelem ((x " ^elem_s^ ") (y " ^elem_s^ ")) " ^bool_s^ " (> x y))\n")


  (* Ordered list predicate definition *)
  let smt_orderlist_def (buf:B.t) (num_addr:int) : unit =
    let idlast = string_of_int num_addr in
    B.add_string buf
      ("(define-fun orderlist" ^idlast^ " ((h " ^heap_s^ ") " ^
       "(a " ^addr_s^ ") (b " ^addr_s^ ")) " ^bool_s^ " \n" ^
       "  true)\n");
    for i = (num_addr-1) downto 1 do
      let id = string_of_int i in
      let idnext = string_of_int (i+1) in
      B.add_string buf
        ("(define-fun orderlist" ^id^ " ((h " ^heap_s^ ") (a " ^addr_s^ ") ( b " ^addr_s^ ")) " ^bool_s^ "\n" ^
         "  (and (isaddr a)\n" ^
         "       (isaddr b)\n" ^
         "       (isaddr (next" ^id^ " h a))\n" ^
         "       (or (= (next" ^id^ " h a) b)\n" ^
         "           (and (lesselem (data (select h (next" ^id^ " h a)))\n" ^
         "                          (data (select h (next" ^idnext^ " h a))))\n" ^
         "                (iselem (data (select h (next" ^id^ " h a))))\n" ^
         "                (iselem (data (select h (next" ^idnext^ " h a))))\n" ^
         "                (isaddr (next" ^idnext^ " h a))\n" ^
         "                (orderlist" ^idnext^ " h a b)))))\n")
    done;
    B.add_string buf
      ("(define-fun orderlist ((h " ^heap_s^ ") (a " ^addr_s^ ") (b " ^addr_s^ ")) " ^bool_s^ "\n" ^
         "  (and (isaddr a)\n" ^
         "       (isaddr b)\n" ^
         "       (or (= a b)\n" ^
         "           (and (lesselem (data (select h a))\n" ^
         "                          (data (select h (next1 h a))))\n" ^
         "                (iselem (data (select h a)))\n" ^
         "                (iselem (data (select h (next1 h a))))\n" ^
         "                (isaddr (next1 h a))\n" ^
         "                (orderlist1 h a b)))))\n")


  let smt_error_def (buf:B.t) : unit =
    let _ = GM.sm_decl_const sort_map "error" cell_s in
      B.add_string buf
        ("(declare-fun error () " ^cell_s^ ")\n" ^
         "(assert (= (lock error) notid))\n" ^
         "(assert (= " ^next "error"^ " null))\n")


  let smt_mkcell_def (buf:B.t) : unit =
    B.add_string buf
      ("") (* Unneeded *)


  let smt_isheap_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun isheap ((h " ^heap_s^ ")) " ^bool_s^ "\n" ^
       "  (= (select h null) error))\n");
    B.add_string buf
      ("(define-fun eqmem ((m1 " ^heap_s^ ") (m2 " ^heap_s^ ")) " ^bool_s^ "\n" ^
       "  (and (forall ((a " ^addr_s^ ")) (=> (not (= a null)) (= (select m1 a) (select m2 a))))\n" ^
       "       (= (select m1 null) error)))\n")


  let smt_nextiter_def (buf:B.t) (num_addr:int) : unit =
      B.add_string  buf
        ("(define-fun next0 ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^addr_s^ " a)\n");
      B.add_string  buf
        ("(define-fun next1 ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^addr_s^ "\n" ^
         "  (next (select h a)))\n");
    for i=2 to num_addr do
      B.add_string buf
        ("(define-fun next"^ (string_of_int i) ^" ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^addr_s^ "\n" ^
         " (next (select h (next"^ (string_of_int (i-1)) ^" h a))))\n")
    done


  let smt_reachable_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun isreachable ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^bool_s^ "\n" ^
       "  (and (isaddr from)\n" ^
       "       (isaddr to)\n" ^
       "       (isaddr (next0 h to))\n" ^
       "       (isaddr (next1 h to))\n");
    for i = 2 to num_addr do
      B.add_string buf
        ("       (isaddr (next" ^(string_of_int i)^ " h to))\n")
    done;
      B.add_string buf
      ("       (or (= from to)\n" ^
       "           (= (next (select h from)) to)\n");
    for i=2 to num_addr do
      B.add_string buf
        ( "\n             (= (next" ^ (string_of_int i)  ^ " h from) to)" )
    done ;
    B.add_string buf ")))\n"


  let smt_address2set_def (buf:B.t) (num_addr:int) : unit =
    let join_sets s1 s2 = "\n  (setunion "^ s1 ^" "^ s2 ^")" in
    B.add_string buf
      ("(define-fun address2set ((h " ^heap_s^ ") (from " ^addr_s^ ")) " ^set_s^ "");
    B.add_string buf
      begin
        match num_addr with
          0 -> "\n  (singleton from))\n"
        | 1 -> "\n  (setunion (singleton from) (singleton (next (select h from)))))\n"
        | _ -> let basic = "\n  (setunion (singleton from) (singleton (next (select h from))))" in
               let addrs = LeapLib.rangeList 2 num_addr in
               let str   = List.fold_left (fun s i ->
                             join_sets ("(singleton (next"^ (string_of_int i) ^ " h from))") s
                           ) basic addrs
               in
                 str^")\n"
      end


  let smt_is_singlepath (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun is_singlepath ((a " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (and (ispath p)\n" ^
       "       (= (length p) 1)\n" ^
       "       (= (select (at p) 0) a)))\n")
   

  let smt_update_heap_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun update_heap ((h " ^heap_s^ ") (a " ^addr_s^ ") (c " ^cell_s^ ")) " ^heap_s^ "\n" ^
       "  (store h a c))\n")

      
  let smt_getp_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun update_pathat ((f PathAt) (i RangeAddress) (a " ^addr_s^ ")) PathAt\n" ^
       "  (ite (is_valid_range_address i) (store f i a) f))\n" ^
       "(define-fun update_pathwhere ((g PathWhere) (a " ^addr_s^ ") (i RangeAddress)) PathWhere\n" ^
       "  (ite (is_valid_range_address i) (store g a i) g))\n" ^
       "(define-fun add_to_path ((p " ^path_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (mkpath (+ 1 (length p))\n" ^
       "          (update_pathat (at p) (length p) a)\n" ^
       "          (update_pathwhere (where p) a (length p))\n" ^
       "          (setunion (addrs p) (singleton a))))\n");
(*
    B.add_string buf
      ("(define-fun update_pathat ((f PathAt) (i RangeAddress) (a " ^addr_s^ ")) PathAt\n" ^
       "  (ite (is_valid_range_address i) (store f i a) f))\n" ^
       "(define-fun update_pathwhere ((g PathWhere) (a " ^addr_s^ ") (i RangeAddress)) PathWhere\n" ^
       "  (ite (is_valid_range_address i) (store g a i) g))\n");
       *)
  (*     "(define-fun add_to_path ((p " ^path_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (mkpath (+ 1 (length p))\n" ^
       "          (update_pathat (at p) (length p) a)\n" ^
       "          (update_pathwhere (where p) a (length p))\n" ^
       "          (setunion (addrs p) (singleton a))))\n");
  *)
    B.add_string buf
      ("(define-fun path0 ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  epsilon)\n");
    B.add_string buf
      ("(define-fun path1 ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (singlepath a))\n");
    for i=2 to (num_addr +1) do
      let stri= string_of_int i in
      let strpre = string_of_int (i-1) in
      B.add_string buf
      ("(define-fun path"^ stri ^" ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (add_to_path (path"^ strpre ^" h a) (next"^ strpre ^" h a)))\n")
    done ;     
    B.add_string buf
      ("(define-fun getp"^ (string_of_int (num_addr + 1)) ^" ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (ite (= (next"^ (string_of_int num_addr) ^" h from) to)\n" ^
       "      (path"^ (string_of_int num_addr) ^" h from)\n" ^
       "      epsilon))\n");
    for i=num_addr downto 1 do
      let stri = string_of_int i in
      let strpre = string_of_int (i-1) in
      let strnext = string_of_int (i+1) in
      B.add_string buf
        ("(define-fun getp"^ stri ^" ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
         "  (ite (= (next"^ strpre ^" h from) to)\n" ^
         "      (path"^ stri ^" h from)\n" ^
         "       (getp"^ strnext ^" h from to)))\n")
    done ;
    B.add_string buf
      ("(define-fun getp ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (getp1 h from to))\n");
    B.add_string buf
      ("(define-fun isgetp ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (eqpath p (getp h from to)))\n")


  let smt_reach_def (buf:B.t) : unit =
    B.add_string buf
      ( "(define-fun reach ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
        "  (and (ispath p)\n" ^
        "    (or (and (= from to)\n" ^
        "             (eqpath p epsilon))\n" ^
        "        (and (not (= from to))\n" ^
        "             (eqpath (getp h from to) p)\n" ^
        "             (not (eqpath p epsilon))))))\n"
      )
      

  let smt_path_length_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun path_length ((p " ^path_s^ ")) RangeAddress (length p))\n")


  let smt_at_path_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun at_path ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
       "  (ite (is_valid_range_address i) (select (at p) i) null))\n")


  let smt_equal_paths_at_def (buf:B.t) : unit =
    B.add_string buf
      ("(define-fun equal_paths_at ((p1 " ^path_s^ ") (i RangeAddress) (p2 " ^path_s^ ") (j RangeAddress)) " ^bool_s^ "\n" ^
       "  (ite (< i (path_length p1))\n" ^
       "      (= (at_path p1 i) (at_path p2 j))\n" ^
       "      true))\n")


  let smt_is_append_def (buf:B.t) (num_addr:int) : unit =
    B.add_string buf
      ("(define-fun is_append ((p1 " ^path_s^ ") (p2 " ^path_s^ ") (p_res " ^path_s^ ")) " ^bool_s^ "\n" ^
       "  (and (= (+ (path_length p1) (path_length p2)) (path_length p_res))");
    for i=0 to num_addr do
      let str_i = (string_of_int i) in
      B.add_string buf 
        ( "\n           (equal_paths_at p1 " ^ str_i ^ " p_res " ^ str_i ^ ")" )
    done ;
    for i=0 to num_addr do
      let str_i = string_of_int i in
      B.add_string buf 
        ( "\n           (equal_paths_at p2 " ^ str_i ^ " p_res (+ (path_length p1) " ^ str_i ^ "))" )
    done ;
    B.add_string buf "))\n"


  (************************* Declarations **************************)



  (********************* Preamble Declaration **********************)
  let update_requirements (req_sorts:Expr.sort list)
                          (req_ops:Expr.special_op_t list)
        : (Expr.sort list * Expr.special_op_t list) =
    let (res_req_sorts, res_req_ops) = (ref req_sorts, ref req_ops) in
  (* If "path" is a required sort, then we need to add "set" as required sort
     since "set" is part of the definition of sort "path" (required by "addrs"
     field) *)
  if (List.mem Expr.Path req_sorts) then
    res_req_sorts := Expr.Set :: !res_req_sorts ;
  (!res_req_sorts, !res_req_ops)


  let smt_preamble buf num_addr num_tid num_elem req_sorts =
    B.add_string buf ";; TLL SMTLib Translation\n";
    if (List.exists (fun s ->
          s=Expr.Addr || s=Expr.Cell || s=Expr.Path || s=Expr.Set || s=Expr.Mem
        ) req_sorts) then smt_addr_preamble buf num_addr ;
    if (List.exists (fun s ->
          s=Expr.Tid || s=Expr.Cell || s=Expr.SetTh || s=Expr.Mem
        ) req_sorts) then smt_tid_preamble buf num_tid ;
    if (List.exists (fun s ->
          s=Expr.Elem || s=Expr.Cell || s=Expr.Mem
        ) req_sorts) then smt_element_preamble buf num_elem ;
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      smt_cell_preamble buf ;
    if List.mem Expr.Mem     req_sorts then smt_heap_preamble buf ;
    if List.mem Expr.Set     req_sorts then smt_set_preamble buf ;
    if List.mem Expr.SetTh   req_sorts then smt_setth_preamble buf ;
    if List.mem Expr.SetElem req_sorts then smt_setelem_preamble buf ;
    if List.mem Expr.Path    req_sorts then smt_path_preamble buf num_addr ;
    if List.mem Expr.Unknown req_sorts then smt_unknown_preamble buf ;
    smt_pos_preamble buf
    

  let smt_defs buf num_addr num_tid num_elem req_sorts req_ops =
    (* Elements *)
    if List.mem Expr.ElemOrder req_ops || List.mem Expr.OrderedList req_ops then
      smt_elemorder_def buf ;
    (* Cells and Heap *)
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      smt_error_def buf ;
    (* Cell *)
    if List.mem Expr.Cell req_sorts then
      begin
        smt_mkcell_def buf ;
        smt_cell_lock buf ;
        smt_cell_unlock_def buf
      end;
    (* Heap *)
    if List.mem Expr.Mem req_sorts then
      begin
        smt_isheap_def buf ;
        smt_dref_def buf ;
        smt_update_heap_def buf
      end;
    (* Sets *)
    if List.mem Expr.Set req_sorts then
      begin
        smt_emp_def buf num_addr ;
        smt_singleton_def buf ;
        smt_union_def buf num_addr ;
        smt_intersection_def buf num_addr ;
        smt_setdiff_def buf num_addr ;
        smt_subseteq_def buf num_addr ;
        smt_eqset_def buf num_addr
      end;
    (* Iterations over next *)
    if List.mem Expr.Addr2Set req_ops
       || List.mem Expr.Reachable req_ops
       || List.mem Expr.Getp req_ops
       || List.mem Expr.OrderedList req_ops then
      smt_nextiter_def buf num_addr ;
    (* Address2set *)
    if List.mem Expr.Addr2Set req_ops then
      begin
        smt_reachable_def buf num_addr ;
        smt_address2set_def buf num_addr
      end;
    (* OrderedList *)
    if List.mem Expr.OrderedList req_ops then smt_orderlist_def buf num_addr ;
    (* Path2set *)
    if List.mem Expr.Path2Set req_ops then smt_path2set_def buf ;
    (* Sets of Threads *)
    if List.mem Expr.SetTh req_sorts then
      begin
        smt_empth_def buf num_tid ;
        smt_singletonth_def buf ;
        smt_unionth_def buf num_tid ;
        smt_intersectionth_def buf num_tid ;
        smt_setdiffth_def buf num_tid ;
        smt_subseteqth_def buf num_tid ;
        smt_eqsetth_def buf num_tid
      end;
    (* Sets of Elements *)
    if List.mem Expr.SetElem req_sorts then
      begin
        smt_empelem_def buf num_elem ;
        smt_singletonelem_def buf ;
        smt_unionelem_def buf num_elem ;
        smt_intersectionelem_def buf num_elem ;
        smt_setdiffelem_def buf num_elem ;
        smt_subseteqelem_def buf num_elem ;
        smt_eqsetelem_def buf num_elem
      end;
    (* Set2Elem *)
    if List.mem Expr.Set2Elem req_ops then smt_settoelems_def buf num_addr ;
    (* Firstlock or Lastlock *)
    if List.mem Expr.FstLocked req_ops ||
       List.mem Expr.LstLocked req_ops ||
       List.mem Expr.Lockset req_ops then
        smt_getlocked_def buf ;
    (* Firstlock *)
    if List.mem Expr.FstLocked req_ops then smt_firstlock_def buf num_addr ;
    (* Lastlock *)
    if List.mem Expr.LstLocked req_ops then smt_lastlock_def buf num_addr ;
    (* Lockset *)
    if List.mem Expr.Lockset req_ops then smt_lockset_def buf num_addr ;
    (* Path *)
    if List.mem Expr.Path req_sorts then
      begin
        smt_rev_def buf num_addr ;
        smt_epsilon_def buf num_addr ;
        smt_ispath_def buf num_addr;
        smt_singletonpath_def buf num_addr ;
        smt_is_singlepath buf ;
        smt_path_length_def buf ;
        smt_at_path_def buf ;
        smt_equal_paths_at_def buf ;
        smt_is_append_def buf num_addr
      end;
    (* Getp *)
    if List.mem Expr.Getp req_ops ||
       List.mem Expr.Reachable req_ops then smt_getp_def buf num_addr ;
    (* Reachable *)
    if List.mem Expr.Reachable req_ops then smt_reach_def buf

  (********************* Preamble Declaration **********************)


  let rec smt_define_var (buf:Buffer.t)
                        (tid_set:VarSet.t)
                        (num_tids:int)
                        (v:Expr.V.t) : unit =
    let s = Expr.V.sort v in
    let sort_str asort = match asort with
                           Expr.Set     -> set_s
                         | Expr.Elem    -> elem_s
                         | Expr.Addr    -> addr_s
                         | Expr.Tid    -> tid_s
                         | Expr.Cell    -> cell_s
                         | Expr.SetTh   -> setth_s
                         | Expr.SetElem -> setelem_s
                         | Expr.Path    -> path_s
                         | Expr.Mem     -> heap_s
                         | Expr.Int     -> int_s
                         | Expr.Bool    -> bool_s
                         | Expr.Unknown -> unk_s in
    let s_str = sort_str s in
    let p_id = match Expr.V.scope v with
               | Expr.V.GlobalScope -> Expr.V.id v
               | Expr.V.Scope proc -> proc ^ "_" ^ (Expr.V.id v) in
    let name = p_id (*if Expr.V.is_primed v then p_id ^ "_prime" else p_id*)
    in
      if Expr.V.is_global v then
        begin
          GM.sm_decl_const sort_map name
            (GM.conv_sort (TllInterface.sort_to_expr_sort s)) ;
          B.add_string buf ( "(declare-fun " ^ name ^ " () " ^ s_str ^ ")\n" );
          match s with
          | Expr.Addr -> B.add_string buf ( "(assert (isaddr " ^name^ "))\n" )
          | Expr.Elem -> B.add_string buf ( "(assert (iselem " ^name^ "))\n" )
          | Expr.Path -> B.add_string buf ( "(assert (ispath " ^name^ "))\n" )
          | Expr.Mem  -> B.add_string buf ( "(assert (isheap " ^name^ "))\n" )
          | Expr.Tid -> B.add_string buf ( "(assert (not (= " ^ name ^ " notid)))\n" );
                         B.add_string buf ( "(assert (istid " ^name^ "))\n" )
(* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)
(*                         B.add_string buf ( "(assert (in_pos_range " ^ name ^ "))\n" ) *)
          | _    -> ()
        end
      else
        begin
          GM.sm_decl_fun sort_map name [tid_s] [s_str] ;
          B.add_string buf ( "(declare-fun " ^ name ^ " () (Array " ^tid_s^ " " ^ s_str ^ "))\n" );
          match s with
          | Expr.Addr -> B.add_string buf ("(assert (isaddr (select " ^name^ " notid)))\n");
                         B.add_string buf ("(assert (isaddr (select " ^name^ " tid_witness)))\n");
                         for i = 1 to num_tids do
                           B.add_string buf ("(assert (isaddr (select " ^name^ " " ^tid_prefix ^ (string_of_int i)^ ")))\n")
                         done
          | Expr.Elem -> B.add_string buf ("(assert (iselem (select " ^name^ " notid)))\n");
                         B.add_string buf ("(assert (iselem (select " ^name^ " tid_witness)))\n");
                         for i = 1 to num_tids do
                           B.add_string buf ("(assert (iselem (select " ^name^ " " ^tid_prefix ^ (string_of_int i)^ ")))\n")
                         done
          | Expr.Path -> VarSet.iter (fun t ->
                           let v_str = variable_invocation_to_str
                                         (Expr.V.set_param v (Expr.V.Local t)) in
                           B.add_string buf ( "(assert (ispath " ^ v_str ^ "))\n" )
                         ) tid_set
          | Expr.Mem -> VarSet.iter (fun t ->
                          let v_str = variable_invocation_to_str
                                        (Expr.V.set_param v (Expr.V.Local t)) in
                          B.add_string buf ( "(assert (isheap " ^ v_str ^ "))\n" )
                        ) tid_set
          | Expr.Tid -> VarSet.iter (fun t ->
                           let v_str = variable_invocation_to_str
                                         (Expr.V.set_param v (Expr.V.Local t)) in
                           B.add_string buf ( "(assert (not (= " ^ v_str ^ " notid)))\n" )
                         ) tid_set;
                         B.add_string buf ("(assert (istid (select " ^name^ " notid)))\n");
                         B.add_string buf ("(assert (istid (select " ^name^ " tid_witness)))\n");
                         for i = 1 to num_tids do
                           B.add_string buf ("(assert (istid (select " ^name^ " " ^tid_prefix ^ (string_of_int i)^ ")))\n")
                         done
          | _    -> ()
          (* FIX: Add iterations for ispath and isheap on local variables *)
        end


  and define_variables (buf:Buffer.t) (num_tids:int) (vars:VarSet.t) : unit =
    let varset     = V.varset_of_sort vars Expr.Set  in
    let varelem    = V.varset_of_sort vars Expr.Elem in
    let varaddr    = V.varset_of_sort vars Expr.Addr in
    let vartid     = V.varset_of_sort vars Expr.Tid in
    let varcell    = V.varset_of_sort vars Expr.Cell in
    let varsetth   = V.varset_of_sort vars Expr.SetTh in
    let varsetelem = V.varset_of_sort vars Expr.SetElem in
    let varpath    = V.varset_of_sort vars Expr.Path in
    let varmem     = V.varset_of_sort vars Expr.Mem  in
    let varint     = V.varset_of_sort vars Expr.Int  in
    let varbool    = V.varset_of_sort vars Expr.Bool  in
    let varunk     = V.varset_of_sort vars Expr.Unknown  in
      VarSet.iter (smt_define_var buf vartid num_tids) varset;
      VarSet.iter (smt_define_var buf vartid num_tids) varelem;
      VarSet.iter (smt_define_var buf vartid num_tids) vartid;
      VarSet.iter (smt_define_var buf vartid num_tids) varaddr;
      VarSet.iter (smt_define_var buf vartid num_tids) varcell;
      VarSet.iter (smt_define_var buf vartid num_tids) varsetth;
      VarSet.iter (smt_define_var buf vartid num_tids) varsetelem;
      VarSet.iter (smt_define_var buf vartid num_tids) varpath;
      VarSet.iter (smt_define_var buf vartid num_tids) varmem;
      VarSet.iter (smt_define_var buf vartid num_tids) varint;
      VarSet.iter (smt_define_var buf vartid num_tids) varbool;
      VarSet.iter (smt_define_var buf vartid num_tids) varunk


  and variables_to_smt (buf:Buffer.t)
                      (num_tids:int)
                      (expr:Expr.conjunctive_formula) : unit =
    let vars = Expr.get_varset_from_conj expr
    in
      define_variables buf num_tids vars


  and variables_from_formula_to_smt (buf:Buffer.t)
                                   (num_tids:int)
                                   (phi:Expr.formula) : unit =
    let vars = Expr.get_varset_from_formula phi
    in
      define_variables buf num_tids vars


  and variable_invocation_to_str (v:Expr.V.t) : string =
    let id = Expr.V.id v in
    let th_str = shared_or_local_to_str (Expr.V.parameter v) in
    let p_str  = match (Expr.V.scope v) with
                 | Expr.V.GlobalScope -> ""
                 | Expr.V.Scope proc -> proc ^ "_" in
    let pr_str = "" in (*if (Expr.V.is_primed v) then "_prime" else "" in *)
    match Expr.V.parameter v with
    | Expr.V.Shared  -> Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
    | Expr.V.Local _ -> Printf.sprintf " (select %s%s%s %s)" p_str id pr_str th_str


  and shared_or_local_to_str (th:Expr.V.shared_or_local) : string =
    match th with
    | Expr.V.Shared -> ""
    | Expr.V.Local t -> variable_invocation_to_str t


  and setterm_to_str (sa:Expr.set) : string =
    match sa with
        Expr.VarSet v       -> variable_invocation_to_str v
      | Expr.EmptySet       -> "empty"
      | Expr.Singl a        -> Printf.sprintf "(singleton %s)" (addrterm_to_str a)
      | Expr.Union(r,s)     -> Printf.sprintf "(setunion %s %s)"
                                                    (setterm_to_str r)
                                                    (setterm_to_str s)
      | Expr.Intr(r,s)      -> Printf.sprintf "(intersection %s %s)"
                                                    (setterm_to_str r)
                                                    (setterm_to_str s)
      | Expr.Setdiff(r,s)   -> Printf.sprintf "(setdiff %s %s)"
                                                    (setterm_to_str r)
                                                    (setterm_to_str s)
      | Expr.PathToSet p    -> Printf.sprintf "(path2set %s)"
                                                    (pathterm_to_str p)
      | Expr.AddrToSet(m,a) -> Printf.sprintf "(address2set %s %s)"
                                                    (memterm_to_str m)
                                                    (addrterm_to_str a)


  and elemterm_to_str (e:Expr.elem) : string =
    match e with
      Expr.VarElem v     -> variable_invocation_to_str v
    | Expr.CellData c    -> let c_str = cellterm_to_str c in
                              data c_str
    | Expr.HavocListElem -> "" (* Don't need a representation for this *)
    | Expr.LowestElem    -> "lowestElem"
    | Expr.HighestElem   -> "highestElem"


  and tidterm_to_str (th:Expr.tid) : string =
    match th with
      Expr.VarTh v      -> variable_invocation_to_str v
    | Expr.NoTid       -> "notid"
    | Expr.CellLockId c -> let c_str = cellterm_to_str c in
                             lock c_str


  and addrterm_to_str (a:Expr.addr) : string =
    match a with
        Expr.VarAddr v        -> variable_invocation_to_str v
      | Expr.Null             -> "null"
      | Expr.Next c           -> Printf.sprintf "(next %s)"
                                    (cellterm_to_str c)
      | Expr.FirstLocked(m,p) -> let m_str = memterm_to_str m in
                                 let p_str = pathterm_to_str p in
                                 Hashtbl.add locked_tbl (m_str, p_str) ();
                                 Printf.sprintf "(firstlock %s %s)" m_str p_str
      | Expr.LastLocked(m,p) -> let m_str = memterm_to_str m in
                                let p_str = pathterm_to_str p in
                                Hashtbl.add locked_tbl (m_str, p_str) ();
                                Printf.sprintf "(lastlock %s %s)" m_str p_str


  and cellterm_to_str (c:Expr.cell) : string =
    match c with
        Expr.VarCell v      -> variable_invocation_to_str v
      | Expr.Error          -> "error"
      | Expr.MkCell(e,a,th) -> Hashtbl.add cell_tbl c ();
                               Printf.sprintf "(mkcell %s %s %s)"
                                        (elemterm_to_str e)
                                        (addrterm_to_str a)
                                        (tidterm_to_str th)
      | Expr.CellLock(c,th) -> Hashtbl.add cell_tbl c ();
                               Printf.sprintf "(cell_lock %s %s)"
                                        (cellterm_to_str c)
                                        (tidterm_to_str th)
      | Expr.CellUnlock c   -> Hashtbl.add cell_tbl c ();
                               Printf.sprintf "(cell_unlock %s)"
                                        (cellterm_to_str c)
      | Expr.CellAt(m,a)    -> Printf.sprintf "(select %s %s)"
                                        (memterm_to_str m)
                                        (addrterm_to_str a)


  and setthterm_to_str (sth:Expr.setth) : string =
    match sth with
        Expr.VarSetTh v       -> variable_invocation_to_str v
      | Expr.EmptySetTh       -> "emptyth"
      | Expr.SinglTh th       -> Printf.sprintf "(singletonth %s)"
                                      (tidterm_to_str th)
      | Expr.UnionTh(rt,st)   -> Printf.sprintf "(unionth %s %s)"
                                      (setthterm_to_str rt)
                                      (setthterm_to_str st)
      | Expr.IntrTh(rt,st)    -> Printf.sprintf "(intersectionth %s %s)"
                                      (setthterm_to_str rt)
                                      (setthterm_to_str st)
      | Expr.SetdiffTh(rt,st) -> Printf.sprintf "(setdiffth %s %s)"
                                      (setthterm_to_str rt)
                                      (setthterm_to_str st)
      | Expr.LockSet(m,p)     -> Printf.sprintf "(lockset %s %s)"
                                      (memterm_to_str m)
                                      (pathterm_to_str p)


  and setelemterm_to_str (se:Expr.setelem) : string =
    match se with
        Expr.VarSetElem v       -> variable_invocation_to_str v
      | Expr.EmptySetElem       -> "emptyelem"
      | Expr.SinglElem e        -> Printf.sprintf "(singletonelem %s)"
                                      (elemterm_to_str e)
      | Expr.UnionElem(rt,st)   -> Printf.sprintf "(unionelem %s %s)"
                                      (setelemterm_to_str rt)
                                      (setelemterm_to_str st)
      | Expr.IntrElem(rt,st)    -> Printf.sprintf "(intersectionelem %s %s)"
                                      (setelemterm_to_str rt)
                                      (setelemterm_to_str st)
      | Expr.SetToElems(s,m)    -> Printf.sprintf "(set2elem %s %s)"
                                      (setterm_to_str s) (memterm_to_str m)
      | Expr.SetdiffElem(rt,st) -> Printf.sprintf "(setdiffelem %s %s)"
                                      (setelemterm_to_str rt)
                                      (setelemterm_to_str st)


  and pathterm_to_str (p:Expr.path) : string =
    match p with
        Expr.VarPath v       -> variable_invocation_to_str v
      | Expr.Epsilon         -> "epsilon"
      | Expr.SimplePath a    -> Printf.sprintf "(singlepath %s)"
                                      (addrterm_to_str a)
      | Expr.GetPath(m,a1,a2)-> let m_str = memterm_to_str m in
                                let a1_str = addrterm_to_str a1 in
                                let a2_str = addrterm_to_str a2 in
                                  Hashtbl.add getp_tbl (m_str, a1_str, a2_str) ();
                                  Printf.sprintf "(getp %s %s %s)" m_str a1_str a2_str


  and memterm_to_str (m:Expr.mem) : string =
    match m with
        Expr.VarMem v      -> variable_invocation_to_str v
      | Expr.Emp           -> "emp"
      | Expr.Update(h,a,c) -> Printf.sprintf "(update_heap %s %s %s)"
                                               (memterm_to_str h)
                                               (addrterm_to_str a)
                                               (cellterm_to_str c)


  and intterm_to_str (i:Expr.integer) : string =
    match i with
      Expr.IntVal j       -> string_of_int j
    | Expr.VarInt v       -> variable_invocation_to_str v
    | Expr.IntNeg j       -> Printf.sprintf "(- %s)" (intterm_to_str j)
    | Expr.IntAdd (j1,j2) -> Printf.sprintf "(+ %s %s)"
                                (intterm_to_str j1) (intterm_to_str j2)
    | Expr.IntSub (j1,j2) -> Printf.sprintf "(- %s %s)"
                                (intterm_to_str j1) (intterm_to_str j2)
    | Expr.IntMul (j1,j2) -> Printf.sprintf "(* %s %s)"
                                (intterm_to_str j1) (intterm_to_str j2)
    | Expr.IntDiv (j1,j2) -> Printf.sprintf "(/ %s %s)"
                                (intterm_to_str j1) (intterm_to_str j2)


  let rec varupdate_to_str (v:Expr.V.t)
                           (th:Expr.tid)
                           (t:Expr.term) : string =
    let v_str = variable_invocation_to_str v in
    let th_str = tidterm_to_str th in
    let t_str = term_to_str t
    in
      Printf.sprintf "(store %s %s %s)" v_str th_str t_str


  and term_to_str (t:Expr.term) : string =
    match t with
      Expr.VarT  v           -> variable_invocation_to_str v
    | Expr.SetT  s           -> setterm_to_str s
    | Expr.ElemT   e         -> elemterm_to_str e
    | Expr.TidT   th        -> tidterm_to_str th
    | Expr.AddrT   a         -> addrterm_to_str a
    | Expr.CellT   c         -> cellterm_to_str c
    | Expr.SetThT sth        -> setthterm_to_str sth
    | Expr.SetElemT se       -> setelemterm_to_str se
    | Expr.PathT   p         -> pathterm_to_str p
    | Expr.MemT  m           -> memterm_to_str m
    | Expr.IntT  i           -> intterm_to_str i
    | Expr.VarUpdate(v,th,t) -> varupdate_to_str v th t


  let append_to_str (p1:Expr.path) (p2:Expr.path) (p3:Expr.path) : string =
    Printf.sprintf "(is_append %s %s %s)" (pathterm_to_str p1)
                                          (pathterm_to_str p2)
                                          (pathterm_to_str p3)


  let reach_to_str (m:Expr.mem) (a1:Expr.addr)
                   (a2:Expr.addr) (p:Expr.path) : string =
    Printf.sprintf "(reach %s %s %s %s)"
      (memterm_to_str m)
      (addrterm_to_str a1)
      (addrterm_to_str a2)
      (pathterm_to_str p)


  let orderlist_to_str (m:Expr.mem) (a1:Expr.addr) (a2:Expr.addr) : string =
    Printf.sprintf ("(orderlist %s %s %s)")
      (memterm_to_str m)
      (addrterm_to_str a1)
      (addrterm_to_str a2)


  let in_to_str (a:Expr.addr) (s:Expr.set) : string =
    Printf.sprintf "(select %s %s)" (setterm_to_str s) (addrterm_to_str a)


  let subseteq_to_str (r:Expr.set) (s:Expr.set) : string =
    Printf.sprintf "(subseteq %s %s)" (setterm_to_str r)
                                      (setterm_to_str s)


  let inth_to_str (t:Expr.tid) (sth:Expr.setth) : string =
    Printf.sprintf "(select %s %s)" (setthterm_to_str sth)
                             (tidterm_to_str t)


  let subseteqth_to_str (r:Expr.setth) (s:Expr.setth) : string =
    Printf.sprintf "(subseteqth %s %s)" (setthterm_to_str r)
                                        (setthterm_to_str s)


  let inelem_to_str (e:Expr.elem) (se:Expr.setelem) : string =
    Printf.sprintf "(select %s %s)" (setelemterm_to_str se)
                                    (elemterm_to_str e)


  let subseteqelem_to_str (r:Expr.setelem) (s:Expr.setelem) : string =
    Printf.sprintf "(subseteqelem %s %s)" (setelemterm_to_str r)
                                          (setelemterm_to_str s)


  let less_to_str (i1:Expr.integer) (i2:Expr.integer) : string =
    Printf.sprintf "(< %s %s)" (intterm_to_str i1) (intterm_to_str i2)


  let lesseq_to_str (i1:Expr.integer) (i2:Expr.integer) : string =
    Printf.sprintf "(<= %s %s)" (intterm_to_str i1) (intterm_to_str i2)


  let greater_to_str (i1:Expr.integer) (i2:Expr.integer) : string =
    Printf.sprintf "(> %s %s)" (intterm_to_str i1) (intterm_to_str i2)


  let greatereq_to_str (i1:Expr.integer) (i2:Expr.integer) : string =
    Printf.sprintf "(>= %s %s)" (intterm_to_str i1) (intterm_to_str i2)


  let lesselem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
    Printf.sprintf "(lesselem %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


  let greaterelem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
    Printf.sprintf "(greaterelem %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


  let eq_to_str (t1:Expr.term) (t2:Expr.term) : string =
    let str_t1 = (term_to_str t1) in
    let str_t2 = (term_to_str t2) in
    match (t1,t2) with
      | (Expr.PathT _, _)    -> Printf.sprintf "(eqpath %s %s)"    str_t1 str_t2
      | (Expr.SetT _, _)     -> Printf.sprintf "(eqset %s %s)"     str_t1 str_t2
      | (Expr.SetThT _, _)   -> Printf.sprintf "(eqsetth %s %s)"   str_t1 str_t2
      | (Expr.SetElemT _, _) -> Printf.sprintf "(eqsetelem %s %s)" str_t1 str_t2
      | (Expr.MemT (Expr.VarMem _ as m1), Expr.MemT (Expr.Update(m2,Expr.Null,_)))
      | (Expr.MemT (Expr.Update(m2,Expr.Null,_)), Expr.MemT (Expr.VarMem _ as m1)) ->
          "(eqmem " ^(memterm_to_str m1)^ " " ^(memterm_to_str m2)^ ")"
      | _                    -> Printf.sprintf "(= %s %s)"         str_t1 str_t2


  let ineq_to_str (t1:Expr.term) (t2:Expr.term) : string =
    let str_t1 = (term_to_str t1) in
    let str_t2 = (term_to_str t2) in
    match t1 with
        Expr.PathT _ -> Printf.sprintf "(not (eqpath %s %s))" str_t1 str_t2
      | _            -> Printf.sprintf "(not (= %s %s))"            str_t1 str_t2


  let pc_to_str (pc:int) (th:Expr.V.shared_or_local) (pr:bool) : string =
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(= (select %s %s) %s)" pc_str th_str (linenum_to_str pc)


  let pcrange_to_str (pc1:int) (pc2:int) (th:Expr.V.shared_or_local) (pr:bool) : string =
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(and (<= %s (select %s %s)) (<= (select %s %s) %s))"
       (linenum_to_str pc1) pc_str th_str pc_str th_str (linenum_to_str pc2)


  let pcupdate_to_str (pc:int) (th:Expr.tid) : string =
    Printf.sprintf "(= %s (store %s %s %s))"
      pc_prime_name Conf.pc_name (tidterm_to_str th) (linenum_to_str pc)


  let smt_partition_assumptions (parts:'a Partition.t list) : string =
    let _ = LeapDebug.debug "entering smt_partition_assumptions...\n" in
    let parts_str =
      List.fold_left (fun str p ->
        let _ = LeapDebug.debug "." in
        let counter = ref 0 in
        let cs = Partition.to_list p in
        let p_str = List.fold_left (fun str c ->
                      let is_null = List.mem (Expr.AddrT Expr.Null) c in
                      let id = if is_null then
                                 "null"
                               else
                                 begin
                                   incr counter;
                                   addr_prefix ^ (string_of_int (!counter))
                                  end in
                      let elems_str = List.fold_left (fun str e ->
                                        str ^ (Printf.sprintf "(= %s %s) "
                                              (term_to_str e) id)
                                      ) "" c in
                      str ^ elems_str
                    ) "" cs in
        str ^ "(and " ^ p_str ^ ")\n"
      ) "" parts
      in
        ("(assert (or " ^ parts_str ^ "))\n")


  let atom_to_str (at:Expr.atom) : string =
    match at with
        Expr.Append(p1,p2,p3)      -> append_to_str p1 p2 p3
      | Expr.Reach(m,a1,a2,p)      -> reach_to_str m a1 a2 p
      | Expr.OrderList(m,a1,a2)    -> orderlist_to_str m a1 a2
      | Expr.In(a,s)               -> in_to_str a s
      | Expr.SubsetEq(r,s)         -> subseteq_to_str r s
      | Expr.InTh(t,st)            -> inth_to_str t st
      | Expr.SubsetEqTh(rt,st)     -> subseteqth_to_str rt st
      | Expr.InElem(e,se)          -> inelem_to_str e se
      | Expr.SubsetEqElem(re,se)   -> subseteqelem_to_str re se
      | Expr.Less(i1,i2)           -> less_to_str i1 i2
      | Expr.LessEq(i1,i2)         -> lesseq_to_str i1 i2
      | Expr.Greater(i1,i2)        -> greater_to_str i1 i2
      | Expr.GreaterEq(i1,i2)      -> greatereq_to_str i1 i2
      | Expr.LessElem(e1,e2)       -> lesselem_to_str e1 e2
      | Expr.GreaterElem(e1,e2)    -> greaterelem_to_str e1 e2
      | Expr.Eq(x,y)               -> eq_to_str x y
      | Expr.InEq(x,y)             -> ineq_to_str x y
      | Expr.BoolVar v             -> variable_invocation_to_str v
      | Expr.PC(pc,t,pr)           -> pc_to_str pc t pr
      | Expr.PCUpdate(pc,t)        -> pcupdate_to_str pc t
      | Expr.PCRange(pc1,pc2,t,pr) -> pcrange_to_str pc1 pc2 t pr


  let literal_to_str (lit:Expr.literal) : string =
    match lit with
        F.Atom(a)    -> (atom_to_str a)
      | F.NegAtom(a) -> ("(not " ^ (atom_to_str a) ^")")

  let rec formula_to_str (phi:Expr.formula) : string =
    let to_smt = formula_to_str in
    match phi with
      F.Literal l       -> literal_to_str l
    | F.True            -> " true "
    | F.False           -> " false "
    | F.And (f1,f2)     -> Printf.sprintf "(and %s %s)" (to_smt f1)
                                                           (to_smt f2)
    | F.Or (f1,f2)      -> Printf.sprintf "(or %s %s)" (to_smt f1)
                                                          (to_smt f2)
    | F.Not f           -> Printf.sprintf "(not %s)"   (to_smt f)
    | F.Implies (f1,f2) -> Printf.sprintf "(=> %s %s)" (to_smt f1)
                                                          (to_smt f2)
    | F.Iff (f1,f2)     -> Printf.sprintf "(= %s %s)" (to_smt f1)
                                                         (to_smt f2)


  let literal_to_smt (buf:Buffer.t) (lit:Expr.literal) : unit =
    B.add_string buf (literal_to_str lit)


  let process_addr (a_expr:string) : string =
    ("(assert (isaddr (next " ^a_expr^ ")))\n")


  let process_tid (t_expr:string) : string =
    ("(assert (istid (lock " ^t_expr^ ")))\n")


  let process_elem (e_expr:string) : string =
    ("(assert (iselem (data " ^e_expr^ ")))\n")


  let process_cell (c:Expr.cell) : string =
    match c with
    | Expr.CellLock (c,t) ->
        let c_str = cellterm_to_str c in
        let t_str = tidterm_to_str t in
          ("(assert (and (= " ^data ("(cell_lock " ^c_str^ " " ^t_str^ ")")^ " " ^data c_str^ ")\n" ^
           "             (= " ^next ("(cell_lock " ^c_str^ " " ^t_str^ ")")^ " " ^next c_str^ ")\n" ^
           "             (= " ^lock ("(cell_lock " ^c_str^ " " ^t_str^ ")")^ " " ^t_str^ ")))\n")
    | Expr.CellUnlock c ->
        let c_str = cellterm_to_str c in
        let notid_str = tidterm_to_str Expr.NoTid in
          ("(assert (and (= " ^data ("(cell_unlock " ^c_str^ ")")^ " " ^data c_str^ ")\n" ^
           "             (= " ^next ("(cell_unlock " ^c_str^ ")")^ " " ^next c_str^ ")\n" ^
           "             (= " ^lock ("(cell_unlock " ^c_str^ ")")^ " " ^notid_str^ ")))\n")
    | Expr.MkCell (e,a,t) ->
        let e_str = elemterm_to_str e in
        let a_str = addrterm_to_str a in
        let t_str = tidterm_to_str t in
        let mkcell_str = "mkcell " ^e_str^ " " ^a_str^ " " ^t_str in
          ("(assert (and (= " ^data ("(" ^mkcell_str^ ")")^ " " ^e_str^ ")\n" ^
           "             (= " ^next ("(" ^mkcell_str^ ")")^ " " ^a_str^ ")\n" ^
           "             (= " ^lock ("(" ^mkcell_str^ ")")^ " " ^t_str^ ")))\n")
    | _ -> raise(UnexpectedCellTerm(Expr.cell_to_str c))


  let process_getp (max_addrs:int) ((m,a1,_):string * string * string) : string =
    let tmpbuf = B.create 1024 in
    B.add_string tmpbuf ("(assert (ispath (path1 " ^m^ " " ^a1^ ")))\n");
    for i = 2 to (max_addrs + 1) do
      let str_i = string_of_int i in
      let str_prev = string_of_int (i-1) in
      B.add_string tmpbuf ("(assert (= (length (path" ^str_i^ " " ^m^ " " ^a1^ ")) (+ 1 (length (path" ^str_prev^ " " ^m^ " " ^a1^ ")))))\n");
      B.add_string tmpbuf ("(assert (= (at (path" ^str_i^ " " ^m^ " " ^a1^ ")) (update_pathat (at (path" ^str_prev^ " " ^m^ " " ^a1^ ")) (length (path" ^str_prev^ " " ^m^ " " ^a1^ ")) (next" ^str_prev^ " " ^m^ " " ^a1^ "))))\n");
      B.add_string tmpbuf ("(assert (= (where (path" ^str_i^ " " ^m^ " " ^a1^ ")) (update_pathwhere (where (path" ^str_prev^ " " ^m^ " " ^a1^ ")) (next" ^str_prev^ " " ^m^ " " ^a1^ ") (length (path" ^str_prev^ " " ^m^ " " ^a1^ ")))))\n");
      B.add_string tmpbuf ("(assert (= (addrs (path" ^str_i^ " " ^m^ " " ^a1^ ")) (store (addrs (path" ^str_prev^ " " ^m^ " " ^a1^ ")) (next" ^str_prev^ " " ^m^ " " ^a1^ ") true)))\n");
      B.add_string tmpbuf ("(assert (ispath (path" ^str_i^ " " ^m^ " " ^a1^ ")))\n")
    done;
    B.contents tmpbuf


  let process_locked (max_addrs:int) ((m,p):string * string) : string =
    let tmpbuf = B.create 1024 in
    for i = 0 to max_addrs do
      B.add_string tmpbuf ("(assert (istid (getlockat " ^m^ " " ^p^ " " ^string_of_int i^ ")))\n")
    done;
    B.contents tmpbuf


  let post_process (buf:B.t) (num_addrs:int) : unit =
    Hashtbl.iter (fun a _ -> B.add_string buf (process_addr a)) addr_tbl;
    Hashtbl.iter (fun e _ -> B.add_string buf (process_elem e)) elem_tbl;
    Hashtbl.iter (fun t _ -> B.add_string buf (process_tid t)) tid_tbl;
    Hashtbl.iter (fun c _ -> B.add_string buf (process_cell c)) cell_tbl;
    Hashtbl.iter (fun g _ -> B.add_string buf (process_getp num_addrs g)) getp_tbl;
    Hashtbl.iter (fun f _ -> B.add_string buf (process_locked num_addrs f)) locked_tbl
    




  let literal_list_to_str (use_q:bool) (ls:Expr.literal list) : string =
    (* The use of quantifiers in SMTLIB remains to be implemented *)
    if use_q then ();
    (* The use of quantifiers in SMTLIB remains to be implemented *)
    clean_lists();
    let _ = GM.clear_sort_map sort_map in
    let expr = F.Conj ls in
    let c = SmpTll.cut_off_normalized expr in
    let num_addr = MS.get c MS.Addr in
    let num_tid = MS.get c MS.Tid in
    let num_elem = MS.get c MS.Elem in
    let (req_sorts, req_ops) =
      List.fold_left (fun (ss,os) lit ->
        let phi = F.Literal lit
        in
          (Expr.required_sorts phi @ ss, Expr.special_ops phi @ os)
      ) ([],[]) ls in
    let (req_sorts, req_ops) = update_requirements req_sorts req_ops in
    let buf = B.create 1024 in
        smt_preamble buf num_addr num_tid num_elem req_sorts;
        smt_defs    buf num_addr num_tid num_elem req_sorts req_ops;
        variables_to_smt buf num_tid expr ;
        let add_and_literal l str =
    "\n         " ^ (literal_to_str l) ^ str
        in
        let formula_str = List.fold_right add_and_literal ls ""
        in
    post_process buf num_addr;
    B.add_string buf "(assert\n   (and";
    B.add_string buf formula_str ;
    B.add_string buf "))\n";
    B.add_string buf "(check-sat)\n" ;
    B.contents   buf


  let formula_to_str (co:Smp.cutoff_strategy_t)
                     (copt:Smp.cutoff_options_t)
                     (use_q:bool)
                     (phi:Expr.formula) : string =
    (* The use of quantifiers in SMTLIB remains to be implemented *)
    if use_q then ();
    (* The use of quantifiers in SMTLIB remains to be implemented *)
    clean_lists();
    let _ = GM.clear_sort_map sort_map in
    verbl _LONG_INFO "**** SMTTllQuery. Will compute the cutoff...\n";
    let max_cut_off = SmpTll.cut_off co copt phi in
    let num_addr    = MS.get max_cut_off MS.Addr in
    let num_tid     = MS.get max_cut_off MS.Tid in
    let num_elem    = MS.get max_cut_off MS.Elem in
    let req_sorts   = Expr.required_sorts phi in
    let req_ops     = Expr.special_ops phi in
    let formula_str = formula_to_str phi in
    let (req_sorts, req_ops) = update_requirements req_sorts req_ops in
    let buf         = B.create 1024
    in
      B.add_string buf (";; Translation for " ^ (Expr.formula_to_str phi) ^ "\n");
      smt_preamble buf num_addr num_tid num_elem req_sorts;
      smt_defs     buf num_addr num_tid num_elem req_sorts req_ops;
      variables_from_formula_to_smt buf num_tid phi ;
      (* We add extra information if needed *)
      post_process buf num_addr;
      B.add_string buf "(assert\n";
      B.add_string buf formula_str ;
      B.add_string buf ")\n";
      B.add_string buf "(check-sat)\n" ;
      B.contents   buf


  let conjformula_to_str (use_q:bool) (expr:Expr.conjunctive_formula) : string =
    match expr with
      F.TrueConj   -> "(assert true)\n(check-sat)"
    | F.FalseConj  -> "(assert false)\n(check-sat)"
    | F.Conj conjs -> literal_list_to_str use_q conjs


  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end

