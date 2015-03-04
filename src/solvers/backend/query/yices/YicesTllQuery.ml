open TllQuery
open LeapLib


module YicesTllQuery : TLL_QUERY =

struct

  module Expr     = TllExpression
  module V        = TllExpression.V
  module VarIdSet = V.VarIdSet
  module VarSet   = V.VarSet
  module B        = Buffer
  module GM       = GenericModel
  module F        = Formula
  module MS       = ModelSize

  let prog_lines = ref 0

  let pc_prime_name : string = Conf.pc_name ^ "_prime"

  let addr_prefix = "aa_"
  let tid_prefix = "tt_"
  let elem_prefix = "ee_"


  (* Sort names *)
  let bool_s    : string = "bool"
  let int_s     : string = "int"
  let addr_s    : string = "address"
  let set_s     : string = "set"
  let elem_s    : string = "elem"
  let tid_s     : string = "thid"
  let cell_s    : string = "cell"
  let setth_s   : string = "setth"
  let setelem_s : string = "setElem"
  let path_s    : string = "path"
  let heap_s    : string = "heap"
  let int_s     : string = "int"
  let unk_s     : string = "unknown"
  let loc_s     : string = "loc"


  (* Information storage *)
  let sort_map : GM.sort_map_t = GM.new_sort_map()


  (* Program lines manipulation *)
  let set_prog_lines (n:int) : unit =
    prog_lines := n


  (************************* Declarations **************************)

  (* (define-type address (scalar null aa_1 aa_2 aa_3 aa_4 aa_5))   *)
  (* (define max_address::int 5)                                    *)
  (* (define-type range_address (subrange 0 max_address))           *)
  let yices_addr_preamble buf num_addr =
    B.add_string buf ("(define-type " ^addr_s^ " (scalar null") ;

    for i = 1 to num_addr do
      B.add_string buf (" " ^ addr_prefix ^ (string_of_int i))
    done ;
    B.add_string buf "))\n" ;
    GM.sm_decl_const sort_map "max_address" int_s ;
    B.add_string buf (
        "(define max_address::" ^int_s^ " " ^ (string_of_int num_addr) ^ ")\n" ^
        "(define-type range_address (subrange 0 max_address))\n")

  (* (define-type tid (scalar NoThread t1 t2 t3)) *)
  (* (define max_tid::int 3)                      *)
  (* (define-type range_tid (subrange 0 max_tid)) *)
  let yices_tid_preamble buf num_tids =
    B.add_string buf ("(define-type " ^tid_s^ " (scalar NoThread") ;
    for i = 1 to num_tids do
      B.add_string buf (" " ^ tid_prefix ^ (string_of_int i))
    done ;
    B.add_string buf "))\n" ;
    GM.sm_decl_const sort_map "max_tid" int_s ;
    B.add_string buf (
        "(define max_tid::" ^int_s^ " " ^ (string_of_int num_tids) ^ ")\n" ^
        "(define-type range_tid (subrange 0 max_tid))\n")

  (* (define-type element) *)
  let yices_element_preamble buf num_elems =
    B.add_string buf ("(define-type " ^elem_s^ " (scalar lowestElem highestElem ") ;
    for i = 1 to num_elems do
      B.add_string buf (" " ^ elem_prefix ^ (string_of_int i))
    done ;
    B.add_string buf ("))\n")
  (*
    B.add_string buf
      ("(define-type " ^elem_s^ "(subrange 1 " ^(string_of_int num_elems)^ "))\n")
  *)

  (* (define-type cell (record data::element next::address lock::tid))   *)
  (* (define next::(-> cell address) (lambda (c::cell) (select c next))) *)
  (* (define data::(-> cell element) (lambda (c::cell) (select c data))) *)
  (* (define lock::(-> cell tid)     (lambda (c::cell) (select c lock))) *)
  let yices_cell_preamble buf =
    B.add_string buf (
       "(define-type " ^cell_s^ " (record data::" ^elem_s^ " " ^
       "                          next::" ^addr_s^ " " ^
       "                          lock::" ^tid_s^ "))\n"   ^
       "(define next::(-> " ^cell_s^ " " ^addr_s^ ") " ^
       "  (lambda (c::" ^cell_s^ ") (select c next)))\n" ^
       "(define data::(-> " ^cell_s^ " " ^elem_s^ ") " ^
       "  (lambda (c::" ^cell_s^ ") (select c data)))\n" ^
       "(define lock::(-> " ^cell_s^ " " ^tid_s^ ")     " ^
       "  (lambda (c::" ^cell_s^ ") (select c lock)))\n" )

  (* (define-type heap    (-> address cell)) *)
  let yices_heap_preamble buf =
    B.add_string buf
      ("(define-type " ^heap_s^ "    (-> " ^addr_s^ " " ^cell_s^ "))\n")

  (* (define-type set     (-> address bool)) *)
  let yices_set_preamble buf =
    B.add_string buf
      ("(define-type " ^set_s^ "     (-> " ^addr_s^ " " ^bool_s^ "))\n")

  (* (define-type setth   (-> tid bool))     *)
  let yices_setth_preamble buf =
    B.add_string buf
      ("(define-type " ^setth_s^ "   (-> " ^tid_s^ " " ^bool_s^ "))\n")

  (* (define-type setelem   (-> elem bool))     *)
  let yices_setelem_preamble buf =
    B.add_string buf
      ("(define-type " ^setelem_s^ "   (-> " ^elem_s^ " " ^bool_s^ "))\n")

  (* (define pathat::(-> range_address address))                     *)
  (* (define pathwhere::(-> address range_address))                  *)
  (* (define-type path                                               *)
  (*   (record length::range_address  at::pathat where::pathwhere))  *)
  (* (define eqpath_pos::(-> path path path_length bool) *)
  (*     (lambda (p::path r::path_length i::range_address) *)
  (*         (=> (and (< i (select p length)) *)
  (*                  (< i (select r length))) *)
  (*             (= ((select p at) i) ((select r at) i))))) *)
  (* (define eqpath::(-> path path bool) *)
  (*     (lambda (p::path r::path) *)
  (*         (and (= (select p length) (select r length)) *)
  (*              (eqpath_pos p r 0) *)
  (*              (eqpath_pos p r 1) *)
  (*              (eqpath_pos p r 2) *)
  (*              (eqpath_pos p r 3)))) *)
  let yices_path_preamble buf num_addr =
    B.add_string buf
      ( "(define-type path_length (subrange 0 (+ 1 max_address)))\n");
    B.add_string buf
      ("(define-type pathat (-> range_address " ^addr_s^ "))\n" ^
       "(define-type pathwhere (-> " ^addr_s^ " range_address))\n" ^
       "(define-type " ^path_s^ "" ^
       "  (record length::path_length at::pathat where::pathwhere))\n") ;
    B.add_string buf
      ("(define eqpath_pos::(-> " ^path_s^ " " ^path_s^ " range_address " ^bool_s^ ")\n" ^
       "    (lambda (p::" ^path_s^ " r::" ^path_s^ " i::range_address)\n" ^
       "        (=> (and (< i (select p length))\n" ^
       "                 (< i (select r length)))\n" ^
       "            (= ((select p at) i) ((select r at) i)))))\n");
    B.add_string buf
      ("(define eqpath::(-> " ^path_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
      "    (lambda (p::" ^path_s^ " r::" ^path_s^ ")\n" ^
      "        (and (= (select p length) (select r length))\n") ;
    for i=0 to num_addr do
      B.add_string buf
        ("             (eqpath_pos p r "^ (string_of_int i) ^ ")\n");
    done ;
    B.add_string buf ")))\n"


  let yices_unknown_preamble buf =
    B.add_string buf
      ("(define-type " ^unk_s^ ")\n")


  let yices_pos_preamble buf =
    B.add_string buf
      (Printf.sprintf "(define-type %s (subrange 1 %i))\n" loc_s !prog_lines);
    GM.sm_decl_fun sort_map Conf.pc_name [tid_s] [loc_s] ;
    GM.sm_decl_fun sort_map pc_prime_name [tid_s] [loc_s] ;
    B.add_string buf ("(define " ^Conf.pc_name^ "::(-> " ^tid_s^ " " ^loc_s^ "))\n");
    B.add_string buf ("(define " ^pc_prime_name^
                          "::(-> " ^tid_s^ " " ^loc_s^ "))\n")


  (* (define subseteq::(-> set set bool)  *)
  (*   (lambda (s1::set s2::set)        *)
  (*     (and (if (s1 null) (s2 null))    *)
  (*          (if (s1 a1) (s2 a1))        *)
  (*          (if (s1 a1) (s2 a2))        *)
  (*          (if (s1 a3) (s2 a3))        *)
  (*          (if (s1 a4) (s2 a4))        *)
  (*          (if (s1 a5) (s2 a5)))))     *)
  let yices_subseteq_def buf num_addr =
    B.add_string buf
      ("(define subseteq::(-> " ^set_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (s1::" ^set_s^ " s2::" ^set_s^ ")\n" ^
       "    (and (=> (s1 null) (s2 null))") ;
      for i=1 to num_addr do
        let aa_i = addr_prefix ^ (string_of_int i) in
        B.add_string buf
    ("\n         (=> (s1 " ^ aa_i ^ ") (s2 " ^ aa_i ^ "))")
      done ;
      B.add_string buf ")))\n"


  (* (define seteq::(-> set set bool)                    *)
  (*   (lambda (s1::set s2::set)                         *)
  (*     (and (ite (s1 null) (s2 null) (not (s2 null)))  *)
  (*          (ite (s1 a1) (s2 a1) (not (s2 a1)))        *)
  (*          (ite (s1 a1) (s2 a2) (not (s2 a2)))        *)
  (*          (ite (s1 a3) (s2 a3) (not (s2 a3)))        *)
  (*          (ite (s1 a4) (s2 a4) (not (s2 a4)))        *)
  (*          (ite (s1 a5) (s2 a5) (not (s2 a5)))))      *)
  let yices_seteq_def buf num_addr =
    B.add_string buf
      ("(define seteq::(-> " ^set_s^ " " ^set_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (s1::" ^set_s^ " s2::" ^set_s^ ")\n" ^
       "    (and (ite (s1 null) (s2 null) (not (s2 null)))") ;
      for i=1 to num_addr do
        let aa_i = addr_prefix ^ (string_of_int i) in
        B.add_string buf
          ("\n         (ite (s1 " ^ aa_i ^ ") (s2 " ^ aa_i ^ ") (not (s2 "
            ^ aa_i ^ ")))")
      done ;
      B.add_string buf ")))\n"



  (* (define singletonth::(-> tid setth)   *)
  (*     (lambda (t::tid)                  *)
  (*         (lambda (r::tid)              *)
  (*             (= t r))))                *)
  let yices_singletonth_def buf =
    B.add_string buf
      ("(define singletonth::(-> " ^tid_s^ " " ^setth_s^ ")\n" ^
       "    (lambda (t::" ^tid_s^ ")\n" ^
       "        (lambda (r::" ^tid_s^ ")\n" ^
       "            (= t r))))\n")

  (* (define unionth::(-> setth setth setth) *)
  (*     (lambda (s::setth r::setth)         *)
  (*         (lambda (t::tid)                *)
  (*             (or (s t) (r t)))))         *)
  let yices_unionth_def buf =
    B.add_string buf
      ("(define unionth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
       "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
       "        (lambda (t::" ^tid_s^ ")\n" ^
       "            (or (s t) (r t)))))\n")

  (* (define intersectionth::(-> setth setth setth) *)
  (*     (lambda (s::setth r::setth)                *)
  (*         (lambda (t::tid)                       *)
  (*             (and (s t) (r t)))))               *)
  let yices_intersectionth_def buf =
    B.add_string buf
      ("(define intersectionth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
       "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
       "        (lambda (t::" ^tid_s^ ")\n" ^
       "            (and (s t) (r t)))))\n")


  (* (define setdiffth::(-> setth setth setth)    *)
  (*     (lambda (s::setth r::setth)              *)
  (*         (lambda (t::tid)                     *)
  (*             (and (s t) (not (r t))))))       *)
  let yices_setdiffth_def buf =
    B.add_string buf
      ("(define setdiffth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
       "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
       "        (lambda (t::" ^tid_s^ ")\n" ^
       "            (and (s t) (not (r t))))))\n")

  (* (define subseteqth::(-> setth setth bool) *)
  (*   (lambda (r::setth) (s::setth)           *)
  (*     (and (if (r NoThread) (s NoThread))   *)
  (*          (if (r t1)       (s t1))         *)
  (*          (if (r t2)       (s t2))         *)
  (*          (if (r t3)       (s t3)))))      *)
  let yices_subseteqth_def buf num_tids =
    B.add_string buf
      ("(define subseteqth::(-> " ^setth_s^ " " ^setth_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (r::" ^setth_s^ " s::" ^setth_s^ ")\n" ^
       "    (and (=> (r NoThread) (s NoThread))\n") ;
    for i=1 to num_tids do
      let tt_i = tid_prefix ^ (string_of_int i) in
        B.add_string buf
    ("\n        (=> (r " ^ tt_i ^ ")       (s " ^ tt_i ^ "))")
    done ;
    B.add_string buf ")))\n"


  (* (define seteqth::(-> setth setth bool)                          *)
  (*   (lambda (s1::setth s2::setth)                                 *)
  (*     (and (ite (s1 NoThread) (s2 NoThread) (not (s2 NoThread)))  *)
  (*          (ite (s1 t1) (s2 t1) (not (s2 t1)))        *)
  (*          (ite (s1 t1) (s2 t2) (not (s2 t2)))        *)
  (*          (ite (s1 t3) (s2 t3) (not (s2 t3)))        *)
  (*          (ite (s1 t4) (s2 t4) (not (s2 t4)))        *)
  (*          (ite (s1 t5) (s2 t5) (not (s2 t5)))))      *)
  let yices_seteqth_def buf num_tids =
    B.add_string buf
      ("(define seteqth::(-> " ^setth_s^ " " ^setth_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (s1::" ^setth_s^ " s2::" ^setth_s^ ")\n" ^
       "    (and (ite (s1 NoThread) (s2 NoThread) (not (s2 NoThread)))") ;
      for i=1 to num_tids do
        let tt_i = tid_prefix ^ (string_of_int i) in
        B.add_string buf
          ("\n         (ite (s1 " ^ tt_i ^ ") (s2 " ^ tt_i ^ ") (not (s2 "
            ^ tt_i ^ ")))")
      done ;
      B.add_string buf ")))\n"


  (* (define singletonelem::(-> elem setelem)   *)
  (*     (lambda (e::elem)                      *)
  (*         (lambda (r::elem)                  *)
  (*             (= e r))))                     *)
  let yices_singletonelem_def buf =
    B.add_string buf
      ("(define singletonelem::(-> " ^elem_s^ " " ^setelem_s^ ")\n" ^
       "    (lambda (e::" ^elem_s^ ")\n" ^
       "        (lambda (r::" ^elem_s^ ")\n" ^
       "            (= e r))))\n")


  (* (define unionelem::(-> setelem setelem setelem) *)
  (*     (lambda (s::setelem r::setelem)             *)
  (*         (lambda (e::elem)                       *)
  (*             (or (s e) (r e)))))                 *)
  let yices_unionelem_def buf =
    B.add_string buf
      ("(define unionelem::(-> " ^setelem_s^ " " ^setelem_s^ " " ^setelem_s^ ")\n" ^
       "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
       "        (lambda (e::" ^elem_s^ ")\n" ^
       "            (or (s e) (r e)))))\n")


  (* (define intersectionelem::(-> setelem setelem setelem) *)
  (*     (lambda (s::setelem r::setelem)                    *)
  (*         (lambda (e::elem)                              *)
  (*             (and (s e) (r e)))))                       *)
  let yices_intersectionelem_def buf =
    B.add_string buf
      ("(define intersectionelem::(-> " ^setelem_s^ " " ^setelem_s^
              " " ^setelem_s^ ")\n" ^
       "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
       "        (lambda (e::" ^elem_s^ ")\n" ^
       "            (and (s e) (r e)))))\n")


  (* (define setdiffelem::(-> setelem setelem setelem)    *)
  (*     (lambda (s::setelem r::setelem)                  *)
  (*         (lambda (e::elem)                            *)
  (*             (and (s e) (not (r e))))))               *)
  let yices_setdiffelem_def buf =
    B.add_string buf
      ("(define setdiffelem::(-> " ^setelem_s^ " " ^setelem_s^
              " " ^setelem_s^ ")\n" ^
       "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
       "        (lambda (e::" ^elem_s^ ")\n" ^
       "            (and (s e) (not (r e))))))\n")


  (* (define subseteqelem::(-> setelem setelem bool) *)
  (*   (lambda (r::setelem) (s::setelem)             *)
  (*     (and (if (r e1) (s e1))                     *)
  (*          (if (r e2) (s e2))                     *)
  (*          (if (r e3) (s e3)))))                  *)
  let yices_subseteqelem_def buf num_elems =
    B.add_string buf
      ("(define subseteqth::(-> " ^setelem_s^ " " ^setelem_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (r::" ^setelem_s^ " s::" ^setelem_s^ ")\n" ^
       "    (and \n") ;
    for i=1 to num_elems do
      let ee_i = elem_prefix ^ (string_of_int i) in
        B.add_string buf
    ("\n        (=> (r " ^ ee_i ^ ") (s " ^ ee_i ^ "))")
    done ;
    B.add_string buf ")))\n"


  (* (define seteqelem::(-> setelem setelem bool)        *)
  (*   (lambda (s1::setelem s2::setelem)                 *)
  (*     (and (ite (s1 e1) (s2 e1) (not (s2 e1)))        *)
  (*          (ite (s1 e1) (s2 e2) (not (s2 e2)))        *)
  (*          (ite (s1 e3) (s2 e3) (not (s2 e3)))        *)
  (*          (ite (s1 e4) (s2 e4) (not (s2 e4)))        *)
  (*          (ite (s1 e5) (s2 e5) (not (s2 e5)))))      *)
  let yices_seteqelem_def buf num_elems =
    B.add_string buf
      ("(define seteqelem::(-> " ^setelem_s^ " " ^setelem_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (s1::" ^setelem_s^ " s2::" ^setelem_s^ ")\n" ^
       "    (and ") ;
      for i=1 to num_elems do
        let ee_i = elem_prefix ^ (string_of_int i) in
        B.add_string buf
          ("\n         (ite (s1 " ^ ee_i ^ ") (s2 " ^ ee_i ^ ") (not (s2 "
            ^ ee_i ^ ")))")
      done ;
      B.add_string buf ")))\n"



  (* (define empty::set)             *)
  (*   (lambda (a::address) (false)) *)

  let yices_emp_def buf =
    GM.sm_decl_const sort_map "empty" set_s ;
    B.add_string buf
      ("(define empty::" ^set_s^ "\n" ^
       "  (lambda (a::" ^addr_s^ ") false))\n")


  (* (define emptyth::setth)         *)
  (*   (lambda (a::address) (false)) *)

  let yices_empth_def buf =
    GM.sm_decl_const sort_map "emptyth" setth_s ;
    B.add_string buf
      ("(define emptyth::" ^setth_s^ "\n" ^
       "  (lambda (t::" ^tid_s^ ") false))\n")


  (* (define emptyth::setth)         *)
  (*   (lambda (a::address) (false)) *)

  let yices_empelem_def buf =
    GM.sm_decl_const sort_map "emptyelem" setelem_s ;
    B.add_string buf
      ("(define emptyelem::" ^setelem_s^ "\n" ^
       "  (lambda (e::" ^elem_s^ ") false))\n")
   

  (* (define intersection::(-> set set set) *)
  (*     (lambda (s::set r::set) *)
  (*         (lambda (a::address) *)
  (*             (and (s a) (r a))))) *)

  let yices_intersection_def buf =
    B.add_string buf
    ("(define intersection::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
     "   (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
     "       (lambda (a::" ^addr_s^ ")\n" ^
     "           (and (s a) (r a)))))\n")


  (* (define set2elem::(-> set mem setelem)             *)
  (*  (lambda (s::set m::mem)                           *)
  (*    (lambda (e::elem)                               *)
  (*      (or (and (= e (data (m null))) (s null))      *)
  (*          (and (= e (data (m aa_1))) (s aa_1))      *)
  (*          (and (= e (data (m aa_2))) (s aa_2))      *)
  (*          (and (= e (data (m aa_3))) (s aa_3))))))  *)
  let yices_settoelems_def buf num_addr =
    B.add_string buf
    ("(define set2elem::(-> " ^set_s^ " " ^heap_s^ " " ^setelem_s^ ")\n" ^
     "  (lambda (s::" ^set_s^ " m::" ^heap_s^ ")\n" ^
     "    (lambda (e::" ^elem_s^ ")\n" ^
     "      (or (and (= e (data (m null))) (s null))\n");
    for i=1 to num_addr do
      let aa_i = addr_prefix ^ (string_of_int i) in
      B.add_string buf
      ("          (and (= e (data (m " ^aa_i^ "))) (s " ^aa_i^ "))\n")
    done ;
    B.add_string buf "))))\n"


  (* (define getlockat::(-> heap path range_address tid)                *)
  (*   (lambda (h::heap p::path i::range_address))                      *)
  (*     (lock (h ((select p at) i))))                                  *)
  (* (define islockedpos::(-> heap path range_address bool)             *)
  (*     (lambda (h::heap p::path i::range_address))                    *)
  (*         (and (< i (select p length)) (/= NoThread (getlockat h p i)))) *)
  (* (define firstlockfrom5::(-> heap path address)                     *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 5) (getlockat h p 5) null)) *)
  (* (define firstlockfrom4::(-> heap path address) *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 4) (getlockat h p 4) (firstlockfrom5 h p))) *)
  (* (define firstlockfrom3::(-> heap path address) *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 3) (getlockat h p 3) (firstlockfrom4 h p))) *)
  (* (define firstlockfrom2::(-> heap path address) *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 2) (getlockat h p 2) (firstlockfrom3 h p))) *)
  (* (define firstlockfrom1::(-> heap path address) *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 1) (getlockat h p 1) (firstlockfrom2 h p))) *)
  (* (define firstlock::(-> heap path address) *)
  (*    (lambda (h::heap p::path)) *)
  (*      (if (islockedpos h p 0) (getlockat h p 0) (firstlockfrom1 h p))) *)

  let yices_firstlock_def buf num_addr =
    let strlast = (string_of_int num_addr) in
    B.add_string buf
      ("(define getlockat::(-> " ^heap_s^ " " ^path_s^ " range_address " ^tid_s^ ")\n" ^
       "  (lambda (h::" ^heap_s^ " p::" ^path_s^ " i::range_address)\n" ^
       "    (lock (h ((select p at) i)))))\n" ^
       "(define getaddrat::(-> " ^path_s^ " range_address " ^tid_s^ ")\n" ^
       "  (lambda (p::" ^path_s^ " i::range_address)\n" ^
       "    ((select p at) i)))\n" ^
       "(define islockedpos::(-> " ^heap_s^ " " ^path_s^ " range_address " ^bool_s^ ")\n" ^
       "    (lambda (h::" ^heap_s^ " p::" ^path_s^ " i::range_address)\n" ^
       "        (and (< i (select p length)) (/= NoThread (getlockat h p i)))))\n" );
    B.add_string buf
      ("(define firstlockfrom" ^ strlast ^
         "::(-> " ^heap_s^ " " ^path_s^ " " ^addr_s^ ")\n" ^
         "   (lambda (h::" ^heap_s^ " p::" ^path_s^ ")\n" ^
         "     (if (islockedpos h p "^ strlast ^") (getaddrat p " ^ strlast ^ ") null)))\n" );
    for i=(num_addr-1) downto 1 do
      let stri    = (string_of_int i) in
      let strnext = (string_of_int (i+1)) in
          B.add_string buf
      ("(define firstlockfrom" ^ stri ^ "::(-> " ^heap_s^ " " ^path_s^ " " ^addr_s^ ")\n" ^
       "   (lambda (h::" ^heap_s^ " p::" ^path_s^ ")\n" ^
       "     (if (islockedpos h p "^ stri ^
              ") (getaddrat p " ^ stri ^ ") (firstlockfrom" ^ strnext ^" h p))))\n")
    done ;
    B.add_string buf
      ("(define firstlock::(-> " ^heap_s^ " " ^path_s^ " " ^addr_s^ ")\n" ^
       "   (lambda (h::" ^heap_s^ " p::" ^path_s^ ")\n" ^
       "     (if (islockedpos h p 0) (getaddrat p 0) (firstlockfrom1 h p))))\n")



  (* (define cell_lock::(-> cell tid cell) *)
  (*   (lambda (c::cell t::tid)) *)
  (*     (mkcell (next c) (data c) t)) *)
  let yices_cell_lock buf =
    B.add_string buf
      ("(define cell_lock::(-> " ^cell_s^ " " ^tid_s^ " " ^cell_s^ ")\n" ^
       "  (lambda (c::" ^cell_s^ " t::" ^tid_s^ ")\n" ^
       "    (mkcell (data c) (next c) t)))\n")

  (* (define cell_unlock::(-> cell cell) *)
  (*   (lambda (c::cell)) *)
  (*     (mkcell (next c) (data c) NoThread)) *)
  let yices_cell_unlock_def buf =
    B.add_string buf
      ("(define cell_unlock::(-> " ^cell_s^ " " ^cell_s^ ")\n" ^
       "  (lambda (c::" ^cell_s^ ")\n" ^
       "    (mkcell (data c) (next c) NoThread)))\n")


  (* (define epsilonat::(-> range_address address) *)
  (*   (lambda r::range_address) null) *)
  (* (define epsilonwhere::(-> address range_address) *)
  (*   (lambda a::address) 0) *)
  (* (define epsilon::path *)
  (*    (mk-record length::0 at::epsilonat where::epsilonwhere)) *)

  let yices_epsilon_def buf =
    GM.sm_decl_const sort_map "epsilon" path_s ;
    B.add_string buf
      ("(define epsilonat::pathat\n" ^
       "  (lambda (r::range_address) null))\n" ^
       "(define epsilonwhere::pathwhere\n" ^
       "  (lambda (a::" ^addr_s^ ") 0))\n" ^
       "(define epsilon::" ^path_s^ "\n" ^
       "   (mk-record length::0 at::epsilonat where::epsilonwhere))\n")


  (* (define singletonat::(-> address range_address address) *)
  (*   (lambda (a::address) *)
  (*     (lambda (r::range_address) *)
  (*       (if (= r 0) a null)))) *)
  (* (define singletonwhere::(-> address address range_address) *)
  (*   (lambda (a::address) *)
  (*     (lambda (b::address) *)
  (*       (if (= a b) 0 1)))) *)
  (* (define singlepath::(-> address path) *)
  (*    (lambda (a::address) *)
  (*      (mk-record length::1 at::(singletonat a) where::(singletonwhere a)))) *)

  let yices_singletonpath_def buf =
    B.add_string buf
      ("(define singletonat::(-> " ^addr_s^ " pathat)\n" ^
       "  (lambda (a::" ^addr_s^ ")\n" ^
       "    (lambda (r::range_address)\n" ^
       "      (if (= r 0) a null))))\n" ^
       "(define singletonwhere::(-> " ^addr_s^ " pathwhere)\n" ^
       "  (lambda (a::" ^addr_s^ ")\n" ^
       "    (lambda (b::" ^addr_s^ ")\n" ^
       "      (if (= a b) 0 1))))\n" ^
       "(define singlepath::(-> " ^addr_s^ " " ^path_s^ ")\n" ^
       "   (lambda (a::" ^ addr_s^ ")\n" ^
       "     (mk-record length::1 at::(singletonat a) " ^
       "        where::(singletonwhere a))))\n")




  (* (define check_position::(-> path range_address bool)                          *)
  (*   (lambda (p::path i::range_address)                                          *)
  (*     (=> (< i (select p length)) (= i ((select p where) ((select p at) i)))))) *)
  (* (define ispath::(-> path bool)      *)
  (*   (lambda (p::path)                 *)
  (*      (and (check_position p 0)      *)
  (*           (check_position p 1)      *)
  (*           (check_position p 2)      *)
  (*           (check_position p 3)      *)
  (*           (check_position p 4)      *)
  (*           (check_position p 5))))   *)
  let yices_ispath_def buf num_addr =
    B.add_string buf
      ("(define check_position::(-> " ^path_s^ " range_address " ^bool_s^ ")\n" ^
       "  (lambda (p::" ^path_s^ " i::range_address)\n" ^
       "    (=> (< i (select p length)) (= i ((select p where) ((select p at) i))))))\n") ;
    B.add_string buf
      ("(define ispath::(-> " ^path_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (p::" ^path_s^ ")\n" ^
       "     (and") ;
    for i=0 to num_addr do
      B.add_string buf 
        ("\n          (check_position p " ^ (string_of_int i) ^ ")")
    done ;
    B.add_string buf ")))\n"

   (* (define rev_position::(-> path path range_address bool)   *)
   (*      (lambda (p::path p_rev::path i::range_address)       *)
   (*          (=> (< (i (select p length)))                    *)
   (*              (= ((select p at) i) ((select p_rev at) (- (select p length) i)))))) *)
   (* (define rev::(-> path path bool)                          *)
   (*     (lambda (p::path p_rev::path)                         *)
   (*     (and (= (select p length) (select p_rev length))      *)
   (*          (rev_position p p_rev 0)                         *)
   (*          (rev_position p p_rev 1)                         *)
   (*          (rev_position p p_rev 2)                         *)
   (*          (rev_position p p_rev 3)                         *)
   (*          (rev_position p p_rev 4)                         *)
   (*          (rev_position p p_rev 5))))                      *)
  let yices_rev_def buf num_addr =
    B.add_string buf
      ( "(define rev_position::(-> "
              ^path_s^ " " ^path_s^ " range_address " ^bool_s^ ")\n" ^
        "  (lambda (p::" ^path_s^ " p_rev::" ^path_s^ " i::range_address)\n" ^
        "     (=> (< i (select p length))\n" ^
        "         (= ((select p at) i) ((select p_rev at) (- (select p length) i))))))\n");
    B.add_string buf
      ("(define rev::(-> " ^path_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (p::" ^path_s^ " p_rev::" ^path_s^ ")\n" ^
       "  (and (= (select p length) (select p_rev length))" );
       for i=0 to num_addr do
         B.add_string buf
     ( "\n      (rev_position p p_rev " ^ (string_of_int i) ^")" )
       done ;
       B.add_string buf ")))\n"

  (* (define path2set::(-> path set)                        *)
  (*     (lambda (p::path)                                  *)
  (*         (lambda (a::address)                           *)
  (*      (< ((select p where) a) (select p length))))) *)
  let yices_path2set_def buf =
    B.add_string buf
      ("(define path2set::(-> " ^path_s^ " " ^set_s^ ")\n" ^
       "    (lambda (p::" ^path_s^ ")\n" ^
       "        (lambda (a::" ^addr_s^ ")\n" ^
       "            (< ((select p where) a) (select p length)))))\n")

  (* (define deref::(-> heap address cell)    *)
  (*     (lambda (h::heap a::address)         *)
  (*         (h a)))                          *)
  let yices_dref_def buf =
    B.add_string buf
      ("(define deref::(-> " ^heap_s^ " " ^addr_s^ " " ^cell_s^ ")\n" ^
       "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ ")\n" ^
       "        (h a)))\n" )


  let yices_elemorder_def buf num_elem =
    B.add_string buf ("(define lesselem::(-> " ^elem_s^ " " ^elem_s^ " " ^bool_s^ "))\n") ;
    B.add_string buf ("(define greaterelem::(-> " ^elem_s^ " " ^elem_s^ " " ^bool_s^ ")\n" ^
                      "  (lambda (x::" ^elem_s^ " y::" ^elem_s^ ")\n" ^
                      "    (lesselem y x)))\n") ;
    (* Totality and no-reflexibility *)
    B.add_string buf ("(assert (not (lesselem lowestElem lowestElem)))\n");
    B.add_string buf ("(assert (not (lesselem highestElem highestElem)))\n");
    B.add_string buf ("(assert (lesselem lowestElem highestElem))\n");
    for i = 1 to num_elem do
      let x = elem_prefix ^ (string_of_int i) in
      
      B.add_string buf ("(assert (not (lesselem " ^x^ " " ^x^ ")))\n") ;
      B.add_string buf ("(assert (lesselem lowestElem " ^x^ "))\n");
      B.add_string buf ("(assert (lesselem " ^x^ " highestElem))\n");
      for j = i+1 to num_elem do
        let y = elem_prefix ^ (string_of_int j) in
          B.add_string buf ("(assert (or (lesselem " ^x^ " " ^y^ ") (lesselem " ^y^ " " ^x^ ")))\n")
      done
    done ;
    (* Transitivity *)
    for i = 1 to num_elem do
      for j = 1 to num_elem do
        for k = 1 to num_elem do
          if (i<>j && j<>k && i<>k) then
            let x = elem_prefix ^ (string_of_int i) in
            let y = elem_prefix ^ (string_of_int j) in
            let z = elem_prefix ^ (string_of_int k) in
            B.add_string buf ("(assert (=> (and (lesselem " ^x^ " " ^y^ ") \
                                                (lesselem " ^y^ " " ^z^ ")) \
                                                (lesselem " ^x^ " " ^z^ ")))\n")
        done
      done
    done


  (* Ordered list predicate definition *)
  let yices_orderlist_def buf num_addr =
    let idlast = string_of_int num_addr in
    B.add_string buf
      ("(define orderlist" ^idlast^ "::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (h::" ^heap_s^ " a::" ^addr_s^ " b::" ^addr_s^ ")\n" ^
       "    true))\n");
    for i = (num_addr-1) downto 1 do
      let id = string_of_int i in
      let idnext = string_of_int (i+1) in
      B.add_string buf
        ("(define orderlist" ^id^ "::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^bool_s^ ")\n" ^
         "  (lambda (h::" ^heap_s^ " a::" ^addr_s^ " b::" ^addr_s^ ")\n" ^
         "    (or (= (next" ^id^ " h a) b)\n" ^
         "        (and (lesselem (data (h (next" ^id^ " h a)))\n" ^
         "                       (data (h (next" ^idnext^ " h a))))\n" ^
         "             (orderlist" ^idnext^ " h a b)))))\n")
    done;
    B.add_string buf
      ("(define orderlist::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^bool_s^ ")\n" ^
       "  (lambda (h::" ^heap_s^ " a::" ^addr_s^ " b::" ^addr_s^ ")\n" ^
       "    (or (= a b)\n" ^
       "        (and (lesselem (data (h a))\n" ^
       "                       (data (h (next1 h a))))\n" ^
       "             (orderlist1 h a b)))))\n")


  (* (define error::cell) *)
  let yices_error_def buf=
    GM.sm_decl_const sort_map "error" cell_s ;
    B.add_string buf ("(define error::" ^cell_s^ ")\n" ^
       "(assert (= (lock error) NoThread))\n" ^
       "(assert (= (next error) null))\n")

  (* (define mkcell::(-> element address tid cell)        *)
  (*     (lambda (h::heap  e::element  a::address k::tid) *)
  (*        (mk-record data::e next::a lock::k)))         *)
  let yices_mkcell_def buf =
    B.add_string buf
      ( "(define mkcell::(-> " ^elem_s^ " " ^addr_s^ " " ^tid_s^ " " ^cell_s^ ")\n" ^
        "   (lambda (e::" ^elem_s^ "  a::" ^addr_s^ " k::" ^tid_s^ ")\n" ^
        "       (mk-record data::e next::a lock::k)))\n" )

  (* (define isheap::(-> heap bool)     *)
  (*     (lambda (h::heap)              *)
  (*         (= (deref h null) error))) *)
  let yices_isheap_def buf =
    B.add_string buf 
      ( "(define isheap::(-> " ^heap_s^ " " ^bool_s^ ")\n" ^
        "    (lambda (h::" ^heap_s^ ")\n" ^
        "        (= (h null) error)))\n")

  (* (define next1::(-> heap address address) (lambda (h::heap a::address) (next h a))) *)
  (* (define next2::(-> address address) (lambda (a::address) (next h (next1 h a)))) *)
  (* (define next3::(-> address address) (lambda (a::address) (next h (next2 h a)))) *)
  (* (define next4::(-> address address) (lambda (a::address) (next h (next3 h a)))) *)
  (* (define next5::(-> address address) (lambda (a::address) (next h (next4 h a)))) *)
  (* (define isreachable::(-> heap address address bool)                         *)
  (*     (lambda (h::heap from::address to::address)                             *)
  (*                  (or (=        from  to)                                    *)
  (*                      (= (next  from) to)                                    *)
  (*                      (= (next2 from) to)                                    *)
  (*                      (= (next3 from) to)                                    *)
  (*                      (= (next4 from) to))))                                 *)
  let yices_nextiter_def buf num_addr =
    (*if (num_addr >= 2) then*)
      B.add_string  buf
        ("(define next0::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ ")\n" ^
         "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ ") a))\n") ;
      B.add_string  buf
        ("(define next1::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ ")\n" ^
         "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ ") (next (h a))))\n") ;
    for i=2 to num_addr do
      B.add_string buf
        ( "(define next" ^ (string_of_int i)
          ^ "::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ ")\n"
          ^ "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ ") "
          ^ "       (next (h (next" ^ (string_of_int (i-1)) ^ " h a)))))\n" )
    done


  let yices_reachable_def buf num_addr =
    B.add_string buf
      ( "(define isreachable::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^bool_s^ ")\n" ^
        "    (lambda (h::" ^heap_s^ " from::" ^addr_s^ " to::" ^addr_s^ ")\n" ^
        "         (or (=        from  to)\n" ^
        "             (= (next (h from)) to)" );
    for i=2 to num_addr do
      B.add_string buf
        ( "\n             (= (next" ^ (string_of_int i)  ^ " h from) to)" ) ; done ;
    B.add_string buf ")))\n"

  (* (define address2set::(-> address set) *)
  (*     (lambda (from::address)           *)
  (*          (lambda (to::address)        *)
  (*              (isreachable from to)))) *)
  let yices_address2set_def buf =
    B.add_string buf
      ( "(define address2set::(-> " ^heap_s^ " " ^addr_s^ " " ^set_s^ ")\n" ^
        "  (lambda (h::" ^heap_s^ " from::" ^addr_s^ ")\n" ^
        "         (lambda (to::" ^addr_s^ ")\n" ^
        "             (isreachable h from to))))\n" )

  (* (define singleton::(-> address set)   *)
  (*     (lambda (a::address)              *)
  (*         (lambda (b::address)          *)
  (*             (= a b))))                *)
  let yices_singleton_def buf =
    B.add_string buf (
        "(define singleton::(-> " ^addr_s^ " " ^set_s^ ")\n" ^
        "    (lambda (a::" ^addr_s^ ")\n" ^
        "        (lambda (b::" ^addr_s^ ")\n" ^
        "            (= a b))))\n" )

  (* (define union::(-> set set set)        *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::address)           *)
  (*             (or (s a) (r a)))))        *)
  let yices_union_def buf =
    B.add_string buf 
      ( "(define union::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^addr_s^ ")\n" ^
        "            (or (s a) (r a)))))\n" )

  (* (define setdiff::(-> set set set)      *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::address)           *) 
  (*             (and (s a) (not (r a)))))) *)
  let yices_setdiff_def buf =
    B.add_string buf 
      ( "(define setdiff::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
        "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
        "        (lambda (a::" ^addr_s^ ")\n" ^
        "            (and (s a) (not (r a))))))\n" )

  (* (define is_singlepath::(-> address path bool) *)
  (*     (lambda (a::address p::path)              *)
  (*         (and (ispath p)                       *)
  (*              (= ((select p length) 1)         *)
  (*              (= ((select p at) 0) a)))))      *)
  let yices_is_singlepath buf =
    B.add_string buf (
        "(define is_singlepath::(-> " ^addr_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
        "    (lambda (a::" ^addr_s^ " p::" ^path_s^ ")\n" ^
        "        (and (ispath p)\n" ^
        "             (= ((select p length) 1)\n" ^
        "             (= ((select p at) 0) a)))))\n" )

  (* (define update_heap::(-> heap address cell heap) *)
  (*     (lambda (h::heap a::address c::cell)         *)
  (*        (update h a c)))                          *)
  let yices_update_heap_def buf =
    B.add_string buf (
        "(define update_heap::(-> " ^heap_s^ " " ^addr_s^ " " ^cell_s^ " " ^heap_s^ ")\n" ^
        "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ " c::" ^cell_s^ ")\n" ^
        "       (update h (a) c)))\n" )


  (* (define update_pathat::(-> pathat range_address address pathat) *)
  (*     (lambda (f::pathat i::range_address a::address) *)
  (*         (lambda (j::range_address) *)
  (*             (if (= i j) a (f j))))) *)
  (* (define update_pathwhere::(-> pathwhere address range_address pathwhere) *)
  (*     (lambda (g::pathwhere a::address i::range_address) *)
  (*         (lambda (b::address) *)
  (*             (if (= b a) i (g b))))) *)
  (* (define add_to_path::(-> path address path) *)
  (*     (lambda (p::path a::address) *)
  (*         (mk-record length::(+ 1 (select p length )) *)
  (*                    at::(update_pathat (select p at) (select p length) a) *)
  (*                    where::(update_pathwhere (select p where) a (select p length))))) *)
  (* (define path1::(-> heap address path) *)
  (*     (lambda (h::heap a::address) *)
  (*         (singlepath a))) *)
  (* (define path2::(-> heap address path) *)
  (*     (lambda (h::heap a::address) *)
  (*         (add_to_path (path1 h a) (next h a)))) *)
  (* (define path3::(-> heap address path) *)
  (*     (lambda (h::heap a::address) *)
  (*         (add_to_path (path2 h a) (next2 h a)))) *)
  (* (define path4::(-> heap address path) *)
  (*     (lambda (h::heap a::address) *)
  (*         (add_to_path (path3 h a) (next3 h a)))) *)
  (* (define getp4::(-> heap address address path) *)
  (*     (lambda (h::heap from::address to::address) *)
  (*         (if (= (next3 h from) to)  *)
  (*             (path4 h from) *)
  (*             epsilon))) *)
  (* (define getp3::(-> heap address address path) *)
  (*     (lambda (h::heap from::address to::address) *)
  (*         (if (= (next2 h from) to)  *)
  (*             (path3 h from) *)
  (*             (getp4 h from to)))) *)
  (* (define getp2::(-> heap address address path) *)
  (*     (lambda (h::heap from::address to::address) *)
  (*         (if (= (next h from) to)  *)
  (*             (path2 h from) *)
  (*             (getp3 h from to)))) *)
  (* (define getp1::(-> heap address address path) *)
  (*     (lambda (h::heap from::address to::address) *)
  (*         (if (= from to)  *)
  (*             (path1 h from) *)
  (*             (getp2 h from to)))) *)
  (* (define getp::(-> heap address address path) *)
  (*     (lambda (h::heap from::address to::address) *)
  (*        (getp1 h from to))) *)
      
  let yices_getp_def buf num_addr =
    B.add_string buf (
      "(define update_pathat::(-> pathat range_address " ^addr_s^ " pathat)\n" ^
      "    (lambda (f::pathat i::range_address a::" ^addr_s^ ")\n" ^
      "        (lambda (j::range_address)\n" ^
      "            (if (= i j) a (f j)))))\n" ^
      "(define update_pathwhere::(-> pathwhere " ^addr_s^ " range_address pathwhere)\n" ^
      "    (lambda (g::pathwhere a::" ^addr_s^ " i::range_address)\n" ^
      "        (lambda (b::" ^addr_s^ ")\n" ^
      "            (if (= b a) i (g b)))))\n" ^
      "(define add_to_path::(-> " ^path_s^ " " ^addr_s^ " " ^path_s^ ")\n" ^
      "    (lambda (p::" ^path_s^ " a::" ^addr_s^ ")\n" ^
      "        (mk-record length::(+ 1 (select p length ))\n" ^
      "                   at::(update_pathat (select p at) (select p length) a)\n" ^
      "                   where::(update_pathwhere (select p where) a (select p length)))))\n");
    B.add_string buf
      ("(define path1::(-> " ^heap_s^ " " ^addr_s^ " " ^path_s^ ")\n" ^
       "     (lambda (h::" ^heap_s^ " a::" ^addr_s^ ")\n" ^
      "        (singlepath a)))\n");
    for i=2 to (num_addr +1) do
      let stri= string_of_int i in
      let strpre = string_of_int (i-1) in
      B.add_string buf 
      ("(define path" ^ stri ^"::(-> " ^heap_s^ " " ^addr_s^ " " ^path_s^ ")\n" ^
      "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ ")\n" ^
      "        (add_to_path (path" ^ strpre ^ " h a) (next" ^ strpre ^ " h a))))\n");
    done ;
    B.add_string buf
      ("(define getp" ^ (string_of_int (num_addr + 1)) ^"::(-> "
                      ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^path_s^ ")\n" ^
       "    (lambda (h::" ^heap_s^ " from::" ^addr_s^ " to::" ^addr_s^ ")\n" ^
       "        (if (= (next" ^ (string_of_int num_addr) ^" h from) to) \n" ^
       "            (path" ^ (string_of_int num_addr) ^" h from)\n" ^
       "            epsilon)))\n");
    for i=num_addr downto 1 do
      let stri = string_of_int i in
      let strpre = string_of_int (i-1) in
      let strnext = string_of_int (i+1) in
      B.add_string buf
        ("(define getp" ^ stri ^ "::(-> " ^heap_s^ " " ^addr_s^ " "
                        ^addr_s^ " " ^path_s^ ")\n" ^
         "    (lambda (h::" ^heap_s^ " from::" ^addr_s^ " to::" ^addr_s^ ")\n" ^
         "        (if (= (next"^ strpre ^" h from) to) \n" ^
         "            (path" ^ stri ^" h from)\n" ^
         "            (getp" ^ strnext ^" h from to))))\n") ;
    done ;
    B.add_string buf
      ("(define getp::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^path_s^ ")\n" ^
       "    (lambda (h::" ^heap_s^ " from::" ^addr_s^ " to::" ^addr_s^ ")\n" ^
       "       (getp1 h from to)))\n") ;
    B.add_string buf
      ("(define isgetp::(-> " ^heap_s^ " " ^addr_s^ " "
                              ^addr_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
       "   (lambda (h::" ^heap_s^ " from::" ^addr_s^
                 " to::" ^addr_s^ " p::" ^path_s^ ")\n" ^
       "      (eqpath p (getp h from to))))\n")


  let yices_reach_def buf =
    B.add_string buf
      ( "(define reach::(-> " ^heap_s^ " " ^addr_s^ " " ^addr_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
        "    (lambda (h::" ^heap_s^ " from::" ^addr_s^ " to::" ^addr_s^ " p::" ^path_s^ ")\n" ^
        "      (and (= (getp h from to) p) (not (= p epsilon)))))\n"
      )



  (* (define path_length::(-> path range_address) *)
  (*     (lambda (p1::path)                       *)
  (*         (select p1 length)))                 *)
  let yices_path_length_def buf =
    B.add_string buf 
      ( "(define path_length::(-> " ^path_s^ " range_address)\n" ^
        "    (lambda (p1::" ^path_s^ ")\n" ^
        "        (select p1 length)))\n" )

  (* (define at_path::(-> path range_address address) *)
  (*     (lambda (p1::path i::range_address)          *)
  (*         ((select p1 at) i)))                     *)
  let yices_at_path_def buf =
    B.add_string buf 
      ( "(define at_path::(-> " ^path_s^ " range_address " ^addr_s^ ")\n" ^
        "    (lambda (p1::" ^path_s^ " i::range_address)\n" ^
        "        ((select p1 at) i)))\n" )


  (* (define equal_paths_at::(-> path range_address path range_address bool) *)
  (*     (lambda (p1::path i::range_address p2::path j::range_address)       *)
  (*         (ite (< i (path_length p1))                                     *)
  (*       (= (at_path p1 i) (at_path p2 j))                             *)
  (*              true)))                                                    *)
  let yices_equal_paths_at_def buf =
    B.add_string buf (
        "(define equal_paths_at::(-> "
              ^path_s^ " range_address " ^path_s^ " range_address " ^bool_s^ ")\n" ^
        "    (lambda (p1::" ^path_s^ " i::range_address p2::"
              ^path_s^ " j::range_address)\n" ^
        "        (ite (< i (path_length p1))\n" ^
        "      (= (at_path p1 i) (at_path p2 j))\n" ^
        "             true)))\n" )


  (* (define is_append::(-> path path path bool)                              *)
  (*    (lambda (p1::path p2::path p_res::path)                               *)
  (*       (and (= (+ (path_length p1) (path_length p2)) (path_length p_res)) *)
  (*            (equal_paths_at p1 0 p_res 0)                                 *)
  (*            (equal_paths_at p1 1 p_res 1)                                 *)
  (*            (equal_paths_at p1 2 p_res 2)                                 *)
  (*            (equal_paths_at p1 3 p_res 3)                                 *)
  (*            (equal_paths_at p1 4 p_res 4)                                 *)
  (*            (equal_paths_at p1 5 p_res 5)                                 *)
  (*            (equal_paths_at p2 0 p_res (+ (path_length p1) 0))            *)
  (*            (equal_paths_at p2 1 p_res (+ (path_length p1) 1))            *)
  (*            (equal_paths_at p2 2 p_res (+ (path_length p1) 2))            *)
  (*            (equal_paths_at p2 3 p_res (+ (path_length p1) 3))            *)
  (*            (equal_paths_at p2 4 p_res (+ (path_length p1) 4))            *)
  (*            (equal_paths_at p2 5 p_res (+ (path_length p1) 5)))))         *)
  let yices_is_append_def buf num_addr =
    B.add_string buf 
      ( "(define is_append::(-> "
          ^path_s^ " " ^path_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
        "   (lambda (p1::" ^path_s^ " p2::" ^path_s^ " p_res::" ^path_s^ ")\n" ^
        "      (and (= (+ (path_length p1) (path_length p2)) (path_length p_res))");
    for i=0 to num_addr do
      let str_i = (string_of_int i) in
      B.add_string buf 
        ( "\n           (equal_paths_at p1 " ^ str_i ^ " p_res " ^ str_i ^ ")" )
    done ;
    for i=0 to num_addr do
      let str_i = string_of_int i in
      B.add_string buf
         ( "\n           (equal_paths_at p2 " ^ str_i ^
                          " p_res (+ (path_length p1) " ^ str_i ^ "))" )
    done ;
    B.add_string buf ")))\n"


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


  let yices_preamble buf num_addr num_tid num_elem req_sorts =
    B.add_string buf ";; TLL Yices Translation";
    if (List.exists (fun s ->
          s=Expr.Addr || s=Expr.Cell || s=Expr.Path || s=Expr.Set || s=Expr.Mem
        ) req_sorts) then yices_addr_preamble buf num_addr ;
    if (List.exists (fun s ->
          s=Expr.Tid || s=Expr.Cell || s=Expr.SetTh
        ) req_sorts) then yices_tid_preamble buf num_tid ;
    if (List.exists (fun s ->
          s=Expr.Elem || s=Expr.Cell || s=Expr.Mem
        ) req_sorts) then yices_element_preamble buf num_elem ;
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      yices_cell_preamble buf ;
    if List.mem Expr.Mem     req_sorts then yices_heap_preamble buf ;
    if List.mem Expr.Set     req_sorts then yices_set_preamble buf ;
    if List.mem Expr.SetTh   req_sorts then yices_setth_preamble buf ;
    if List.mem Expr.SetElem req_sorts then yices_setelem_preamble buf ;
    if List.mem Expr.Path    req_sorts then begin
                                              yices_path_preamble buf num_addr ;
                                              yices_ispath_def buf num_addr
                                            end;
    if List.mem Expr.Unknown req_sorts then yices_unknown_preamble buf ;
    yices_pos_preamble buf


  let yices_defs buf num_addr num_tid num_elem req_sorts req_ops =
    (* Elements *)
    if List.mem Expr.ElemOrder req_ops || List.mem Expr.OrderedList req_ops then
      yices_elemorder_def buf num_elem ;
    (* Cells and Heap *)
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      yices_error_def buf ;
    (* Cell *)
    if List.mem Expr.Cell req_sorts then
      begin
        yices_mkcell_def buf ;
        yices_cell_lock buf ;
        yices_cell_unlock_def buf
      end;
    (* Heap *)
    if List.mem Expr.Mem req_sorts then
      begin
        yices_isheap_def buf ;
        yices_dref_def buf ;
        yices_update_heap_def buf
      end;
    (* Sets *)
    if List.mem Expr.Set req_sorts then
      begin
        yices_emp_def buf ;
        yices_singleton_def buf ;
        yices_union_def buf ;
        yices_intersection_def buf ;
        yices_setdiff_def buf ;
        yices_subseteq_def buf num_addr ;
        yices_seteq_def buf num_addr
      end;
    (* Iterations over next *)
    if List.mem Expr.Addr2Set req_ops || List.mem Expr.OrderedList req_ops then
      yices_nextiter_def buf num_addr ;
    (* Address2set *)
    if List.mem Expr.Addr2Set req_ops then
      begin
        yices_reachable_def buf num_addr ;
        yices_address2set_def buf
      end;
    (* OrderedList *)
    if List.mem Expr.OrderedList req_ops then yices_orderlist_def buf num_addr ;
    (* Path2set *)
    if List.mem Expr.Path2Set req_ops then yices_path2set_def buf ;
    (* Sets of Threads *)
    if List.mem Expr.SetTh req_sorts then
      begin
        yices_empth_def buf ;
        yices_singletonth_def buf ;
        yices_unionth_def buf ;
        yices_intersectionth_def buf ;
        yices_setdiffth_def buf ;
        yices_subseteqth_def buf num_tid ;
        yices_seteqth_def buf num_tid ;
      end;
    (* Sets of Elements *)
    if List.mem Expr.SetElem req_sorts then
      begin
        yices_empelem_def buf ;
        yices_singletonelem_def buf ;
        yices_unionelem_def buf ;
        yices_intersectionelem_def buf ;
        yices_setdiffelem_def buf ;
        yices_subseteqelem_def buf num_elem ;
        yices_seteqelem_def buf num_elem ;
      end;
    (* Set2Elem *)
    if List.mem Expr.Set2Elem req_ops then yices_settoelems_def buf num_addr ;
    (* Firstlock *)
    if List.mem Expr.FstLocked req_ops then yices_firstlock_def buf num_addr ;
    (* Path *)
    if List.mem Expr.Path req_sorts then
      begin
        yices_rev_def buf num_addr ;
        yices_epsilon_def buf ;
        yices_singletonpath_def buf ;
        yices_is_singlepath buf ;
        yices_path_length_def buf ;
        yices_at_path_def buf ;
        yices_equal_paths_at_def buf ;
        yices_is_append_def buf num_addr
      end;
    (* Getp *)
    if List.mem Expr.Getp req_ops then yices_getp_def buf num_addr ;
    (* Reachable *)
    if List.mem Expr.Reachable req_ops then yices_reach_def buf


  (********************* Preamble Declaration **********************)


  let rec yices_define_var (buf:Buffer.t)
                           (tid_set:Expr.V.VarSet.t)
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
    let name = if Expr.V.is_primed v then p_id ^ "'" else p_id
    in
      if Expr.V.is_global v then
        begin
          GM.sm_decl_const sort_map name
            (GM.conv_sort (TllInterface.sort_to_expr_sort s));
          B.add_string buf ( "(define " ^ name ^ "::" ^ s_str ^ ")\n" );
          match s with
            Expr.Path -> B.add_string buf ( "(assert (ispath " ^ name ^ "))\n" )
          | Expr.Mem  -> B.add_string buf ( "(assert (isheap " ^ name ^ "))\n" )
          | Expr.Tid -> B.add_string buf ( "(assert (/= "^ name ^" NoThread))\n")
          | _    -> ()
        end
      else
        begin
          GM.sm_decl_fun sort_map name [tid_s] [s_str] ;
          B.add_string buf ( "(define " ^ name ^ "::(-> " ^tid_s^ " " ^ s_str ^ "))\n" );
          match s with
            Expr.Path -> Expr.V.VarSet.iter (fun t ->
                      let v_str = variable_invocation_to_str
                                      (Expr.V.set_param v (Expr.V.Local t)) in
                        B.add_string buf ( "(assert (ispath " ^ v_str ^ "))\n" )
                    ) tid_set
          | Expr.Mem -> Expr.V.VarSet.iter (fun t ->
                      let v_str = variable_invocation_to_str
                                      (Expr.V.set_param v (Expr.V.Local t)) in
                        B.add_string buf ( "(assert (isheap " ^ v_str ^ "))\n" )
                    ) tid_set
          | Expr.Tid -> Expr.V.VarSet.iter (fun t ->
                      let v_str = variable_invocation_to_str
                                      (Expr.V.set_param v (Expr.V.Local t)) in
                        B.add_string buf ( "(assert (/= " ^ v_str ^ " NoThread))\n" )
                    ) tid_set
          | _    -> ()
          (* FIX: Add iterations for ispath and isheap on local variables *)
        end


  and define_variables (buf:Buffer.t) (vars:Expr.V.VarSet.t) : unit =
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
    let varunk     = V.varset_of_sort vars Expr.Unknown  in
      VarSet.iter (yices_define_var buf vartid) varset;
      VarSet.iter (yices_define_var buf vartid) varelem;
      VarSet.iter (yices_define_var buf vartid) vartid;
      VarSet.iter (yices_define_var buf vartid) varaddr;
      VarSet.iter (yices_define_var buf vartid) varcell;
      VarSet.iter (yices_define_var buf vartid) varsetth;
      VarSet.iter (yices_define_var buf vartid) varsetelem;
      VarSet.iter (yices_define_var buf vartid) varpath;
      VarSet.iter (yices_define_var buf vartid) varmem;
      VarSet.iter (yices_define_var buf vartid) varint;
      VarSet.iter (yices_define_var buf vartid) varunk


  and variables_to_yices (buf:Buffer.t) (expr:Expr.conjunctive_formula) : unit =
    let vars = Expr.get_varset_from_conj expr
    in
      define_variables buf vars


  and variables_from_formula_to_yices (buf:Buffer.t)
                                      (phi:Expr.formula) : unit =
    let vars = Expr.get_varset_from_formula phi
    in
      define_variables buf vars


  and variable_invocation_to_str (v:Expr.V.t) : string =
    let id = Expr.V.id v in
    let th_str = shared_or_local_to_str (Expr.V.parameter v) in
    let p_str  = match (Expr.V.scope v) with
                 | Expr.V.GlobalScope -> ""
                 | Expr.V.Scope proc -> proc ^ "_" in
    let pr_str = if Expr.V.is_primed v then "'" else "" in
    match Expr.V.parameter v with
    | Expr.V.Shared ->  Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
    | Expr.V.Local _ -> Printf.sprintf " (%s%s%s %s)" p_str id pr_str th_str


  and shared_or_local_to_str (th:Expr.V.shared_or_local) : string =
    match th with
    | Expr.V.Shared -> ""
    | Expr.V.Local t -> variable_invocation_to_str t


  and setterm_to_str (s:Expr.set) : string =
    match s with
        Expr.VarSet v -> variable_invocation_to_str v
      | Expr.EmptySet -> "empty"
      | Expr.Singl a  -> Printf.sprintf "(singleton %s)" (addrterm_to_str a)
      | Expr.Union(r,s) -> Printf.sprintf "(union %s %s)" (setterm_to_str r)
                                                          (setterm_to_str s)
      | Expr.Intr(r,s)       -> Printf.sprintf "(intersection %s %s)"
                                                          (setterm_to_str r)
                                                          (setterm_to_str s)
      | Expr.Setdiff(r,s)  -> Printf.sprintf "(setdiff %s %s)"
                                                          (setterm_to_str r)
                                                          (setterm_to_str s)
      | Expr.PathToSet p     -> Printf.sprintf "(path2set %s)"
                                                        (pathterm_to_str p)
      | Expr.AddrToSet(m,a) -> Printf.sprintf "(address2set %s %s)"
                                                        (memterm_to_str m)
                                                        (addrterm_to_str a)


  and elemterm_to_str (e:Expr.elem) : string =
    match e with
      Expr.VarElem v     -> variable_invocation_to_str v
    | Expr.CellData c    -> Printf.sprintf "(data %s)" (cellterm_to_str c)
    | Expr.HavocListElem -> "" (* Don't need representation for this statement *)
    | Expr.LowestElem    -> "lowestElem"
    | Expr.HighestElem   -> "highestElem"


  and tidterm_to_str (th:Expr.tid) : string =
    match th with
      Expr.VarTh v      -> variable_invocation_to_str v
    | Expr.NoTid       -> "NoThread"
    | Expr.CellLockId c -> Printf.sprintf "(lock %s)" (cellterm_to_str c)


  and addrterm_to_str (a:Expr.addr) : string =
    match a with
        Expr.VarAddr v        -> variable_invocation_to_str v
      | Expr.Null             -> "null"
      | Expr.Next c           -> Printf.sprintf "(next %s)"
                                    (cellterm_to_str c)
      | Expr.FirstLocked(m,p) -> Printf.sprintf "(firstlock %s %s)"
                                    (memterm_to_str m)
                                    (pathterm_to_str p)


  and cellterm_to_str (c:Expr.cell) : string =
    match c with
        Expr.VarCell v      -> variable_invocation_to_str v
      | Expr.Error          -> "error"
      | Expr.MkCell(e,a,th) -> Printf.sprintf "(mkcell %s %s %s)"
                                        (elemterm_to_str e)
                                        (addrterm_to_str a)
                                        (tidterm_to_str th)
      | Expr.CellLock(c,th) -> Printf.sprintf "(cell_lock %s %s)"
                                        (cellterm_to_str c)
                                        (tidterm_to_str th)
      | Expr.CellUnlock c  -> Printf.sprintf "(cell_unlock %s)"
                                        (cellterm_to_str c)
      | Expr.CellAt(m,a)     -> Printf.sprintf "(%s %s)"
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
      | Expr.GetPath(m,a1,a2)-> Printf.sprintf "(getp %s %s %s)"
                                      (memterm_to_str m)
                                      (addrterm_to_str a1)
                                      (addrterm_to_str a2)


  and memterm_to_str (m:Expr.mem) : string =
    match m with
        Expr.VarMem v      -> variable_invocation_to_str v
      | Expr.Emp           -> "emp"
      | Expr.Update(m,a,c) -> Printf.sprintf "(update_heap %s %s %s)"
                                            (memterm_to_str m)
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
      Printf.sprintf "(update %s (%s) %s)" v_str th_str t_str


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
    Printf.sprintf "(orderlist %s %s %s)"
      (memterm_to_str m)
      (addrterm_to_str a1)
      (addrterm_to_str a2)


  let in_to_str (a:Expr.addr) (s:Expr.set) : string =
    Printf.sprintf "(%s %s)"  (setterm_to_str s) (addrterm_to_str a)


  let subseteq_to_str (r:Expr.set) (s:Expr.set) : string =
    Printf.sprintf "(subseteq %s %s)" (setterm_to_str r)
                                      (setterm_to_str s)


  let inth_to_str (t:Expr.tid) (sth:Expr.setth) : string =
    Printf.sprintf "(%s %s)" (setthterm_to_str sth)
                             (tidterm_to_str t)


  let subseteqth_to_str (r:Expr.setth) (s:Expr.setth) : string =
    Printf.sprintf "(subseteqth %s %s)" (setthterm_to_str r)
                                        (setthterm_to_str s)


  let inelem_to_str (e:Expr.elem) (se:Expr.setelem) : string =
    Printf.sprintf "(%s %s)" (setelemterm_to_str se)
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
    Printf.sprintf "(lesselem %s %s)" (elemterm_to_str e1)
                                      (elemterm_to_str e2)

  let greaterelem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
    Printf.sprintf "(greaterelem %s %s)" (elemterm_to_str e1)
                                         (elemterm_to_str e2)

  let eq_to_str (t1:Expr.term) (t2:Expr.term) : string =
    let str_t1 = (term_to_str t1) in
    let str_t2 = (term_to_str t2) in
    match t1 with
      | Expr.PathT _ -> Printf.sprintf "(eqpath %s %s)"  str_t1 str_t2
      | Expr.SetT _  -> Printf.sprintf "(seteq %s %s)"   str_t1 str_t2
      | Expr.SetThT _-> Printf.sprintf "(seteqth %s %s)" str_t1 str_t2
      | _            -> Printf.sprintf "(= %s %s)"       str_t1 str_t2


  let ineq_to_str (t1:Expr.term) (t2:Expr.term) : string =
    let str_t1 = (term_to_str t1) in
    let str_t2 = (term_to_str t2) in
    match t1 with
      | Expr.PathT _ -> Printf.sprintf "(not (eqpath %s %s))"  str_t1 str_t2
      | Expr.SetT  _ -> Printf.sprintf "(not (seteq %s %s))"   str_t1 str_t2
      | Expr.SetThT _-> Printf.sprintf "(not (seteqth %s %s))" str_t1 str_t2
      | _            -> Printf.sprintf "(/= %s %s)"            str_t1 str_t2


  let pc_to_str (pc:int) (th:Expr.V.shared_or_local) (pr:bool) : string =
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(= (%s %s) %i)" pc_str th_str pc


  let pcrange_to_str (pc1:int) (pc2:int) (th:Expr.V.shared_or_local) (pr:bool) : string =
    let pc_str = if pr then pc_prime_name else Conf.pc_name in
    let th_str = shared_or_local_to_str th
    in
      Printf.sprintf "(and (<= %i (%s %s)) (<= (%s %s) %i))"
                     pc1 pc_str th_str pc_str th_str pc2


  let pcupdate_to_str (pc:int) (th:Expr.tid) : string =
    Printf.sprintf "(= %s (update %s (%s) %i))"
      pc_prime_name Conf.pc_name (tidterm_to_str th) pc


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
    let to_yices = formula_to_str in
    match phi with
      F.Literal l       -> literal_to_str l
    | F.True            -> " true "
    | F.False           -> " false "
    | F.And (f1,f2)     -> Printf.sprintf "(and %s %s)" (to_yices f1)
                                                           (to_yices f2)
    | F.Or (f1,f2)      -> Printf.sprintf "(or %s %s)" (to_yices f1)
                                                          (to_yices f2)
    | F.Not f           -> Printf.sprintf "(not %s)"   (to_yices f)
    | F.Implies (f1,f2) -> Printf.sprintf "(=> %s %s)" (to_yices f1)
                                                          (to_yices f2)
    | F.Iff (f1,f2)     -> Printf.sprintf "(= %s %s)" (to_yices f1)
                                                         (to_yices f2)


  let literal_to_yices (buf:Buffer.t) (lit:Expr.literal) : unit =
    B.add_string buf (literal_to_str lit)


  let literal_list_to_str (use_q:bool) (ls:Expr.literal list) : string =
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
        yices_preamble buf num_addr num_tid num_elem req_sorts;
        yices_defs     buf num_addr num_tid num_elem req_sorts req_ops;
        variables_to_yices buf expr ;
        let add_and_literal l str =
    "\n         " ^ (literal_to_str l) ^ str
        in
        let formula_str = List.fold_right add_and_literal ls ""
        in
    B.add_string buf "(assert+\n    (and";
    B.add_string buf formula_str ;
    B.add_string buf "))\n(check)" ;
    B.contents   buf


  let formula_to_str (co:Smp.cutoff_strategy_t)
                     (copt:Smp.cutoff_options_t)
                     (use_q:bool)
                     (phi:Expr.formula) : string =
    let _ = GM.clear_sort_map sort_map in
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
      yices_preamble                  buf num_addr num_tid num_elem req_sorts;
      yices_defs                      buf num_addr num_tid num_elem
                                          req_sorts req_ops;
      variables_from_formula_to_yices buf phi ;
      B.add_string buf "(assert+\n";
      B.add_string buf formula_str ;
      B.add_string buf ")\n(check)" ;
      B.contents   buf


  let conjformula_to_str (use_q:bool) (expr:Expr.conjunctive_formula) : string =
    match expr with
      F.TrueConj   -> "(assert+ true)\n(check)"
    | F.FalseConj  -> "(assert+ false)\n(check)"
    | F.Conj conjs -> literal_list_to_str use_q conjs


  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end
