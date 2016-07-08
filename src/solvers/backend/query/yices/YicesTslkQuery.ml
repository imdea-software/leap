
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


open LeapLib


module Make (TSLK : TSLKExpression.S) =
  struct

    module Expr     = TSLK
    module VarIdSet = TSLK.VarIdSet
    module Smp      = SmpTslk.Make(TSLK)
    module B        = Buffer
    module GM       = GenericModel
    module Interf   = TSLKInterface.Make(TSLK)


    let prog_lines = ref 0

    let pc_prime_name : string = Conf.pc_name ^ "_prime"

    let addr_prefix = "aa_"
    let tid_prefix = "tt_"
    let elem_prefix = "ee_"


    (* Sort names *)
    let bool_s    : string = "bool"
    let int_s     : string = "int"
    let level_s   : string = "level"
    let addr_s    : string = "address"
    let set_s     : string = "set"
    let elem_s    : string = "elem"
    let tid_s     : string = "thid"
    let cell_s    : string = "cell"
    let setth_s   : string = "setth"
    let setelem_s : string = "setElem"
    let path_s    : string = "path"
    let heap_s    : string = "heap"
    let unk_s     : string = "unknown"
    let loc_s     : string = "loc"


    (* Information storage *)
    let sort_map : GM.sort_map_t = GM.new_sort_map()


    (************************* Declarations **************************)
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


    let yices_element_preamble buf num_elems =
      B.add_string buf ("(define-type " ^elem_s^ " (scalar lowestElem highestElem ") ;
      for i = 1 to num_elems do
        B.add_string buf (" " ^ elem_prefix ^ (string_of_int i))
      done ;
      B.add_string buf ("))\n")
    (* B.add_string buf
         ("(define-type " ^elem_s^ "(subrange 1 " ^(string_of_int num_elems)^ "))\n")
       (define-type cell (record data::element next::address lock::tid))
       (define next::(-> cell address) (lambda (c::cell) (select c next)))
       (define data::(-> cell element) (lambda (c::cell) (select c data)))
       (define lock::(-> cell tid)     (lambda (c::cell) (select c lock))) *)
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


    let yices_heap_preamble buf =
      B.add_string buf
        ("(define-type " ^heap_s^ "    (-> " ^addr_s^ " " ^cell_s^ "))\n")


    let yices_set_preamble buf =
      B.add_string buf
        ("(define-type " ^set_s^ "     (-> " ^addr_s^ " " ^bool_s^ "))\n")

    
    let yices_setth_preamble buf =
      B.add_string buf
        ("(define-type " ^setth_s^ "   (-> " ^tid_s^ " " ^bool_s^ "))\n")

    
    let yices_setelem_preamble buf =
      B.add_string buf
        ("(define-type " ^setelem_s^ "   (-> " ^elem_s^ " " ^bool_s^ "))\n")


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


    let yices_singletonth_def buf =
      B.add_string buf
        ("(define singletonth::(-> " ^tid_s^ " " ^setth_s^ ")\n" ^
         "    (lambda (t::" ^tid_s^ ")\n" ^
         "        (lambda (r::" ^tid_s^ ")\n" ^
         "            (= t r))))\n")


    let yices_unionth_def buf =
      B.add_string buf
        ("(define unionth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
         "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
         "        (lambda (t::" ^tid_s^ ")\n" ^
         "            (or (s t) (r t)))))\n")


    let yices_intersectionth_def buf =
      B.add_string buf
        ("(define intersectionth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
         "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
         "        (lambda (t::" ^tid_s^ ")\n" ^
         "            (and (s t) (r t)))))\n")


    let yices_setdiffth_def buf =
      B.add_string buf
        ("(define setdiffth::(-> " ^setth_s^ " " ^setth_s^ " " ^setth_s^ ")\n" ^
         "    (lambda (s::" ^setth_s^ " r::" ^setth_s^ ")\n" ^
         "        (lambda (t::" ^tid_s^ ")\n" ^
         "            (and (s t) (not (r t))))))\n")


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


    let yices_singletonelem_def buf =
      B.add_string buf
        ("(define singletonelem::(-> " ^elem_s^ " " ^setelem_s^ ")\n" ^
         "    (lambda (e::" ^elem_s^ ")\n" ^
         "        (lambda (r::" ^elem_s^ ")\n" ^
         "            (= e r))))\n")


    let yices_unionelem_def buf =
      B.add_string buf
        ("(define unionelem::(-> " ^setelem_s^ " " ^setelem_s^ " " ^setelem_s^ ")\n" ^
         "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
         "        (lambda (e::" ^elem_s^ ")\n" ^
         "            (or (s e) (r e)))))\n")


    let yices_intersectionelem_def buf =
      B.add_string buf
        ("(define intersectionelem::(-> " ^setelem_s^ " " ^setelem_s^
                " " ^setelem_s^ ")\n" ^
         "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
         "        (lambda (e::" ^elem_s^ ")\n" ^
         "            (and (s e) (r e)))))\n")


    let yices_setdiffelem_def buf =
      B.add_string buf
        ("(define setdiffelem::(-> " ^setelem_s^ " " ^setelem_s^
                " " ^setelem_s^ ")\n" ^
         "    (lambda (s::" ^setelem_s^ " r::" ^setelem_s^ ")\n" ^
         "        (lambda (e::" ^elem_s^ ")\n" ^
         "            (and (s e) (not (r e))))))\n")


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



    let yices_emp_def buf =
      GM.sm_decl_const sort_map "empty" set_s ;
      B.add_string buf
        ("(define empty::" ^set_s^ "\n" ^
         "  (lambda (a::" ^addr_s^ ") false))\n")


    let yices_empth_def buf =
      GM.sm_decl_const sort_map "emptyth" setth_s ;
      B.add_string buf
        ("(define emptyth::" ^setth_s^ "\n" ^
         "  (lambda (t::" ^tid_s^ ") false))\n")


    let yices_empelem_def buf =
      GM.sm_decl_const sort_map "emptyelem" setelem_s ;
      B.add_string buf
        ("(define emptyelem::" ^setelem_s^ "\n" ^
         "  (lambda (e::" ^elem_s^ ") false))\n")
     

    let yices_intersection_def buf =
      B.add_string buf
      ("(define intersection::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
       "   (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
       "       (lambda (a::" ^addr_s^ ")\n" ^
       "           (and (s a) (r a)))))\n")


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


    let yices_cell_lock buf =
      B.add_string buf
        ("(define cell_lock::(-> " ^cell_s^ " " ^tid_s^ " " ^cell_s^ ")\n" ^
         "  (lambda (c::" ^cell_s^ " t::" ^tid_s^ ")\n" ^
         "    (mkcell (data c) (next c) t)))\n")


    let yices_cell_unlock_def buf =
      B.add_string buf
        ("(define cell_unlock::(-> " ^cell_s^ " " ^cell_s^ ")\n" ^
         "  (lambda (c::" ^cell_s^ ")\n" ^
         "    (mkcell (data c) (next c) NoThread)))\n")


    let yices_epsilon_def buf =
      GM.sm_decl_const sort_map "epsilon" path_s ;
      B.add_string buf
        ("(define epsilonat::pathat\n" ^
         "  (lambda (r::range_address) null))\n" ^
         "(define epsilonwhere::pathwhere\n" ^
         "  (lambda (a::" ^addr_s^ ") 0))\n" ^
         "(define epsilon::" ^path_s^ "\n" ^
         "   (mk-record length::0 at::epsilonat where::epsilonwhere))\n")


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


    let yices_path2set_def buf =
      B.add_string buf
        ("(define path2set::(-> " ^path_s^ " " ^set_s^ ")\n" ^
         "    (lambda (p::" ^path_s^ ")\n" ^
         "        (lambda (a::" ^addr_s^ ")\n" ^
         "            (< ((select p where) a) (select p length)))))\n")


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


    let yices_error_def buf=
      GM.sm_decl_const sort_map "error" cell_s ;
      B.add_string buf ("(define error::" ^cell_s^ ")\n" ^
         "(assert (= (lock error) NoThread))\n" ^
         "(assert (= (next error) null))\n")


    let yices_mkcell_def buf =
      B.add_string buf
        ( "(define mkcell::(-> " ^elem_s^ " " ^addr_s^ " " ^tid_s^ " " ^cell_s^ ")\n" ^
          "   (lambda (e::" ^elem_s^ "  a::" ^addr_s^ " k::" ^tid_s^ ")\n" ^
          "       (mk-record data::e next::a lock::k)))\n" )


    let yices_isheap_def buf =
      B.add_string buf 
        ( "(define isheap::(-> " ^heap_s^ " " ^bool_s^ ")\n" ^
          "    (lambda (h::" ^heap_s^ ")\n" ^
          "        (= (h null) error)))\n")

    
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


    let yices_address2set_def buf =
      B.add_string buf
        ( "(define address2set::(-> " ^heap_s^ " " ^addr_s^ " " ^set_s^ ")\n" ^
          "  (lambda (h::" ^heap_s^ " from::" ^addr_s^ ")\n" ^
          "         (lambda (to::" ^addr_s^ ")\n" ^
          "             (isreachable h from to))))\n" )


    let yices_singleton_def buf =
      B.add_string buf (
          "(define singleton::(-> " ^addr_s^ " " ^set_s^ ")\n" ^
          "    (lambda (a::" ^addr_s^ ")\n" ^
          "        (lambda (b::" ^addr_s^ ")\n" ^
          "            (= a b))))\n" )


    let yices_union_def buf =
      B.add_string buf 
        ( "(define union::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
          "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
          "        (lambda (a::" ^addr_s^ ")\n" ^
          "            (or (s a) (r a)))))\n" )


    let yices_setdiff_def buf =
      B.add_string buf 
        ( "(define setdiff::(-> " ^set_s^ " " ^set_s^ " " ^set_s^ ")\n" ^
          "    (lambda (s::" ^set_s^ " r::" ^set_s^ ")\n" ^
          "        (lambda (a::" ^addr_s^ ")\n" ^
          "            (and (s a) (not (r a))))))\n" )

    
    let yices_is_singlepath buf =
      B.add_string buf (
          "(define is_singlepath::(-> " ^addr_s^ " " ^path_s^ " " ^bool_s^ ")\n" ^
          "    (lambda (a::" ^addr_s^ " p::" ^path_s^ ")\n" ^
          "        (and (ispath p)\n" ^
          "             (= ((select p length) 1)\n" ^
          "             (= ((select p at) 0) a)))))\n" )


    let yices_update_heap_def buf =
      B.add_string buf (
          "(define update_heap::(-> " ^heap_s^ " " ^addr_s^ " " ^cell_s^ " " ^heap_s^ ")\n" ^
          "    (lambda (h::" ^heap_s^ " a::" ^addr_s^ " c::" ^cell_s^ ")\n" ^
          "       (update h (a) c)))\n" )


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


    let yices_path_length_def buf =
      B.add_string buf 
        ( "(define path_length::(-> " ^path_s^ " range_address)\n" ^
          "    (lambda (p1::" ^path_s^ ")\n" ^
          "        (select p1 length)))\n" )


    let yices_at_path_def buf =
      B.add_string buf 
        ( "(define at_path::(-> " ^path_s^ " range_address " ^addr_s^ ")\n" ^
          "    (lambda (p1::" ^path_s^ " i::range_address)\n" ^
          "        ((select p1 at) i)))\n" )


    let yices_equal_paths_at_def buf =
      B.add_string buf (
          "(define equal_paths_at::(-> "
                ^path_s^ " range_address " ^path_s^ " range_address " ^bool_s^ ")\n" ^
          "    (lambda (p1::" ^path_s^ " i::range_address p2::"
                ^path_s^ " j::range_address)\n" ^
          "        (ite (< i (path_length p1))\n" ^
          "      (= (at_path p1 i) (at_path p2 j))\n" ^
          "             true)))\n" )



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
    (* ALE: If "path" is a required sort, then we need to add "set" as required
       sort since "set" is part of the definition of sort "path" (required by
       "addrs" field) *)
    if (List.mem Expr.Path req_sorts) then
      res_req_sorts := Expr.Set :: !res_req_sorts ;
    (!res_req_sorts, !res_req_ops)


    let yices_preamble buf num_addr num_tid num_elem req_sorts =
      if (List.exists (fun s ->
            s=Expr.Addr || s=Expr.Cell || s=Expr.Path || s=Expr.Set || s=Expr.Mem
          ) req_sorts) then yices_addr_preamble buf num_addr ;
      if (List.exists (fun s ->
            s=Expr.Tid || s=Expr.Cell || s=Expr.SetTh
          ) req_sorts) then yices_tid_preamble buf num_tid ;
      if (List.exists (fun s ->
            s=Expr.Elem || s=Expr.Cell || s=Expr.Mem
          ) req_sorts) then yices_element_preamble buf num_elem ;
      if List.mem Expr.Cell    req_sorts then yices_cell_preamble buf ;
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
      (* Cell *)
      if List.mem Expr.Cell req_sorts then
        begin
          yices_error_def buf ;
          yices_mkcell_def buf ;
          yices_cell_lock buf ;
          yices_cell_unlock_def buf
        end;
      (* Heap *)
      if List.mem Expr.Cell req_sorts then
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
      let (id,s,pr,th,p) = v in
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
                           | Expr.Level   -> level_s
                           | Expr.Unknown -> unk_s in
      let s_str = sort_str s in
      let p_id = Option.map_default (fun str -> str ^ "_" ^ id) id p in
      let name = if pr then p_id ^ "'" else p_id
      in
        if Expr.V.is_global v then
          begin
            GM.sm_decl_const sort_map name
              (GM.conv_sort (Interf.sort_to_expr_sort s)) ;
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
                                        (Expr.V.set_param v (Expr.VarTh t)) in
                          B.add_string buf ( "(assert (ispath " ^ v_str ^ "))\n" )
                      ) tid_set
            | Expr.Mem -> Expr.V.VarSet.iter (fun t ->
                        let v_str = variable_invocation_to_str
                                        (Expr.V.set_param v (Expr.VarTh t)) in
                          B.add_string buf ( "(assert (isheap " ^ v_str ^ "))\n" )
                      ) tid_set
            | Expr.Tid -> Expr.V.VarSet.iter (fun t ->
                        let v_str = variable_invocation_to_str
                                        (Expr.V.set_param v (Expr.VarTh t)) in
                          B.add_string buf ( "(assert (/= " ^ v_str ^ " NoThread))\n" )
                      ) tid_set
            | _    -> ()
            (* FIX: Add iterations for ispath and isheap on local variables *)
          end


    and define_variables (buf:Buffer.t) (vars:Expr.V.VarSet.t) : unit =
      let varset     = Expr.varset_of_sort vars Expr.Set  in
      let varelem    = Expr.varset_of_sort vars Expr.Elem in
      let varaddr    = Expr.varset_of_sort vars Expr.Addr in
      let vartid     = Expr.varset_of_sort vars Expr.Tid in
      let varcell    = Expr.varset_of_sort vars Expr.Cell in
      let varsetth   = Expr.varset_of_sort vars Expr.SetTh in
      let varsetelem = Expr.varset_of_sort vars Expr.SetElem in
      let varpath    = Expr.varset_of_sort vars Expr.Path in
      let varmem     = Expr.varset_of_sort vars Expr.Mem  in
      let varunk     = Expr.varset_of_sort vars Expr.Unknown  in
        Expr.V.VarSet.iter (yices_define_var buf vartid) varset;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varelem;
        Expr.V.VarSet.iter (yices_define_var buf vartid) vartid;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varaddr;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varcell;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varsetth;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varsetelem;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varpath;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varmem;
        Expr.V.VarSet.iter (yices_define_var buf vartid) varunk


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
      let (id,s,pr,th,p) = v in
      let th_str = Option.map_default tidterm_to_str "" th in
      let p_str  = Option.map_default (fun n -> Printf.sprintf "%s_" n) "" p in
      let pr_str = if pr then "'" else ""
      in
        if th = None then
          Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
        else
          Printf.sprintf " (%s%s%s %s)" p_str id pr_str th_str


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
        Expr.VarElem v         -> variable_invocation_to_str v
      | Expr.CellData c        -> Printf.sprintf "(data %s)" (cellterm_to_str c)
      | Expr.HavocSkiplistElem -> "" (* ALE: No need of a representation for this statement. *)
      | Expr.LowestElem    -> "lowestElem"
      | Expr.HighestElem   -> "highestElem"


    and tidterm_to_str (th:Expr.tid) : string =
      match th with
        Expr.VarTh v            -> variable_invocation_to_str v
      | Expr.NoTid             -> "NoThread"
      | Expr.CellLockIdAt (c,l) -> Printf.sprintf "(lock_at %s %s)" (cellterm_to_str c)
                                                                    (levelterm_to_str l)


    and addrterm_to_str (a:Expr.addr) : string =
      match a with
          Expr.VarAddr v        -> variable_invocation_to_str v
        | Expr.Null             -> "null"
        | Expr.ArrAt (c,l)     -> Printf.sprintf "(next_at %s %s)"
                                      (cellterm_to_str c)
                                      (levelterm_to_str l)
        | Expr.FirstLocked(m,p) -> Printf.sprintf "(firstlock %s %s)"
                                      (memterm_to_str m)
                                      (pathterm_to_str p)


    and cellterm_to_str (c:Expr.cell) : string =
      match c with
          Expr.VarCell v          -> variable_invocation_to_str v
        | Expr.Error              -> "error"
        | Expr.MkCell(e,aa,tt,l)  -> Printf.sprintf "(mkcell %s %s %s %s)"
                                          (elemterm_to_str e)
                                          (String.concat " " (List.map addrterm_to_str aa))
                                          (String.concat " " (List.map tidterm_to_str tt))
                                          (levelterm_to_str l)
        | Expr.CellLockAt(c,l,th) -> Printf.sprintf "(cell_lock_at %s %s %s)"
                                          (cellterm_to_str c)
                                          (levelterm_to_str l)
                                          (tidterm_to_str th)
        | Expr.CellUnlockAt (c,l) -> Printf.sprintf "(cell_unlock_at %s %s)"
                                          (cellterm_to_str c)
                                          (levelterm_to_str l)
        | Expr.CellAt(m,a)        -> Printf.sprintf "(%s %s)"
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


    and levelterm_to_str (l:Expr.level) : string =
      match l with
      | Expr.LevelVal n  -> "ll_" ^ string_of_int n
      | Expr.VarLevel v  -> variable_invocation_to_str v
      | Expr.LevelSucc l -> Printf.sprintf "(lsucc %s)" (levelterm_to_str l)
      | Expr.LevelPred l -> Printf.sprintf "(lpred %s)" (levelterm_to_str l)
      | Expr.HavocLevel  -> "" (* ALE: No need of a representation for this statement. *)



    let rec term_to_str (t:Expr.term) : string =
      match t with
        Expr.VarT  v           -> variable_invocation_to_str v
      | Expr.SetT  s           -> setterm_to_str s
      | Expr.ElemT   e         -> elemterm_to_str e
      | Expr.TidT   th         -> tidterm_to_str th
      | Expr.AddrT   a         -> addrterm_to_str a
      | Expr.CellT   c         -> cellterm_to_str c
      | Expr.SetThT sth        -> setthterm_to_str sth
      | Expr.SetElemT se       -> setelemterm_to_str se
      | Expr.PathT   p         -> pathterm_to_str p
      | Expr.MemT  m           -> memterm_to_str m
      | Expr.LevelT l          -> levelterm_to_str l


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


    let lesslevel_to_str (l1:Expr.level) (l2:Expr.level) : string =
      Printf.sprintf "(less_l %s %s)" (levelterm_to_str l1)
                                      (levelterm_to_str l2)


    let lesseqlevel_to_str (l1:Expr.level) (l2:Expr.level) : string =
      Printf.sprintf "(lesseq_l %s %s)" (levelterm_to_str l1)
                                        (levelterm_to_str l2)


    let greaterlevel_to_str (l1:Expr.level) (l2:Expr.level) : string =
      Printf.sprintf "(great_l %s %s)" (levelterm_to_str l1)
                                       (levelterm_to_str l2)


    let greatereqlevel_to_str (l1:Expr.level) (l2:Expr.level) : string =
      Printf.sprintf "(greateq_l %s %s)" (levelterm_to_str l1)
                                         (levelterm_to_str l2)


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


    let pc_to_str (pc:int) (th:Expr.tid option) (pr:bool) : string =
      let pc_str = if pr then pc_prime_name else Conf.pc_name
      in
        Printf.sprintf "(= (%s %s) %i)" pc_str
            (Option.map_default tidterm_to_str "" th) pc


    let pcrange_to_str (pc1:int) (pc2:int)
                             (th:Expr.tid option) (pr:bool) : string =
      let pc_str = if pr then pc_prime_name else Conf.pc_name in
      let th_str = Option.map_default tidterm_to_str "" th
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
        | Expr.Less(l1,l2)           -> lesslevel_to_str l1 l2
        | Expr.LessEq(l1,l2)         -> lesseqlevel_to_str l1 l2
        | Expr.Greater(l1,l2)        -> greaterlevel_to_str l1 l2
        | Expr.GreaterEq(l1,l2)      -> greatereqlevel_to_str l1 l2
        | Expr.LessElem(e1,e2)       -> lesselem_to_str e1 e2
        | Expr.GreaterElem(e1,e2)    -> greaterelem_to_str e1 e2
        | Expr.Eq(x,y)               -> eq_to_str x y
        | Expr.InEq(x,y)             -> ineq_to_str x y
        | Expr.PC(pc,t,pr)           -> pc_to_str pc t pr
        | Expr.PCUpdate(pc,t)        -> pcupdate_to_str pc t
        | Expr.PCRange(pc1,pc2,t,pr) -> pcrange_to_str pc1 pc2 t pr


    let literal_to_str (lit:Expr.literal) : string =
      match lit with
          Expr.Atom(a)    -> (atom_to_str a)
        | Expr.NegAtom(a) -> ("(not " ^ (atom_to_str a) ^")")

    let rec formula_to_str (phi:Expr.formula) : string =
      let to_yices = formula_to_str in
      match phi with
        Expr.Literal l       -> literal_to_str l
      | Expr.True            -> " true "
      | Expr.False           -> " false "
      | Expr.And (f1,f2)     -> Printf.sprintf "(and %s %s)" (to_yices f1)
                                                             (to_yices f2)
      | Expr.Or (f1,f2)      -> Printf.sprintf "(or %s %s)" (to_yices f1)
                                                            (to_yices f2)
      | Expr.Not f           -> Printf.sprintf "(not %s)"   (to_yices f)
      | Expr.Implies (f1,f2) -> Printf.sprintf "(=> %s %s)" (to_yices f1)
                                                            (to_yices f2)
      | Expr.Iff (f1,f2)     -> Printf.sprintf "(= %s %s)" (to_yices f1)
                                                           (to_yices f2)


    let literal_to_yices (buf:Buffer.t) (lit:Expr.literal) : unit =
      B.add_string buf (literal_to_str lit)


    let literal_list_to_str (ls:Expr.literal list) : string =
      let _ = GM.clear_sort_map sort_map in
      let expr = Expr.Conj ls in
      let c = Smp.cut_off_normalized expr in
      let num_addr = c.SmpTslk.num_addrs in
      let num_tid = c.SmpTslk.num_tids in
      let num_elem = c.SmpTslk.num_elems in
      let (req_sorts, req_ops) =
        List.fold_left (fun (ss,os) lit ->
          let phi = Expr.Literal lit
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


    let formula_to_str (stac:Tactics.solva_tactic option)
                       (co:SmpTslk.cutoff_strategy_t)
                       (copt:SmpTslk.cutoff_options_t)
                       (phi:Expr.formula) : string =
      let _ = GM.clear_sort_map sort_map in
      let max_cut_off = Smp.cut_off co copt phi in
      let num_addr    = max_cut_off.SmpTslk.num_addrs in
      let num_tid     = max_cut_off.SmpTslk.num_tids in
      let num_elem    = max_cut_off.SmpTslk.num_elems in
      let req_sorts   = Expr.required_sorts phi in
      let req_ops     = Expr.special_ops phi in
      let formula_str = formula_to_str phi in
      let (req_sorts, req_ops) = update_requirements req_sorts req_ops in
      let buf         = B.create 1024
      in
        yices_preamble                  buf num_addr num_tid num_elem req_sorts;
        yices_defs                      buf num_addr num_tid num_elem
                                            req_sorts req_ops;
        variables_from_formula_to_yices buf phi ;
        B.add_string buf "(assert+\n";
        B.add_string buf formula_str ;
        B.add_string buf ")\n(check)" ;
        B.contents   buf


    let conjformula_to_str (expr:Expr.conjunctive_formula) : string =
      match expr with
        Expr.TrueConj   -> "(assert+ true)\n(check)"
      | Expr.FalseConj  -> "(assert+ false)\n(check)"
      | Expr.Conj conjs -> literal_list_to_str conjs


    let get_sort_map () : GM.sort_map_t =
      GM.copy_sort_map sort_map
  end
