open LeapLib
open LeapVerbose

module Expr     = TllExpression
module VarIdSet = TllExpression.VarIdSet
module B        = Buffer
module GM       = GenericModel

exception UnexpectedCellTerm of string
exception UnexpectedSetTerm of string
exception UnexpectedSetthTerm of string
exception UnexpectedSetelemTerm of string

let prog_lines = ref 0


let pc_name        : string = "pc"
let pc_prime_name  : string = pc_name ^ "_prime"
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
let tid_s     : string = "Thid"
let cell_s    : string = "Cell"
let setth_s   : string = "Setth"
let setelem_s : string = "SetElem"
let path_s    : string = "Path"
let heap_s    : string = "Heap"
let unk_s     : string = "Unknown"
let loc_s     : string = "Loc"


(* Lock-Unlock information table *)
(* We store calls to cell_lock and cell_unlock in the formula, in order to
	 add the necessary assertions once we have translated the formula *)
let cell_list = ref []
let set_list = ref []
let setth_list = ref []
let setelem_list = ref []
let addr_list = ref []
let elem_list = ref []
let tid_list = ref []

let clean_lists () :  unit =
	cell_list := [];
	set_list := [];
	setth_list := [];
	setelem_list := [];
	addr_list := [];
	elem_list := [];
	tid_list := []


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
	elem_list := expr :: !elem_list;
	("(data " ^expr^ ")")


let next(expr:string) : string =
	addr_list := expr :: !addr_list;
	("(next " ^expr^ ")")


let lock(expr:string) : string =
	tid_list := expr :: !tid_list;
	("(lock " ^expr^ ")")


(* (define-type address (scalar null aa_1 aa_2 aa_3 aa_4 aa_5))   *)
(* (define max_address::int 5)                                    *)
(* (define-type range_address (subrange 0 max_address))           *)
let z3_addr_preamble buf num_addr =
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


(* (define-type tid (scalar notid t1 t2 t3)) *)
(* (define max_tid::int 3)                      *)
(* (define-type range_tid (subrange 0 max_tid)) *)
let z3_tid_preamble buf num_tids =
	B.add_string buf ("(define-sort " ^tid_s^ " () " ^int_s^ ")\n");
	GM.sm_decl_const sort_map "max_tid" int_s ;
	B.add_string buf ("(define-fun max_tid () " ^int_s^ " " ^(string_of_int num_tids)^ ")\n");
	B.add_string buf
		("(define-fun notid () " ^addr_s^ " 0)\n");
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
let z3_element_preamble buf num_elems =
	B.add_string buf ("(define-sort " ^elem_s^ " () " ^int_s^ ")\n");
	B.add_string buf ("(define-fun lowestElem () " ^elem_s^ " 0)\n");
	B.add_string buf ("(define-fun highestElem () " ^elem_s^ " " ^(string_of_int (num_elems+1))^ ")\n");
	for i = 1 to num_elems do
		let i_str = string_of_int i in
		let e_str = elem_prefix ^ i_str in
		B.add_string buf ("(define-fun " ^e_str^ " () " ^elem_s^ " " ^i_str^ ")\n")
	done;
	B.add_string buf ("(define-fun iselem ((x " ^elem_s^ ")) " ^bool_s^ " (and (<= lowestElem x) (<= x highestElem)))\n")




(* (define-type cell (record data::element next::address lock::tid))   *)
(* (define next::(-> cell address) (lambda (c::cell) (select c next))) *)
(* (define data::(-> cell element) (lambda (c::cell) (select c data))) *)
(* (define lock::(-> cell tid)     (lambda (c::cell) (select c lock))) *)
let z3_cell_preamble buf =
	B.add_string buf
		("(declare-sort " ^cell_s^ ")\n\
			(declare-fun mkcell ((" ^elem_s^ ") (" ^addr_s^ ") (" ^tid_s^ ")) " ^cell_s^ ")\n\
			(declare-fun data (" ^cell_s^ ") " ^elem_s^ ")\n\
			(declare-fun next (" ^cell_s^ ") " ^addr_s^ ")\n\
			(declare-fun lock (" ^cell_s^ ") " ^tid_s^ ")\n")


(* (define-type heap    (-> address cell)) *)
let z3_heap_preamble buf =
  B.add_string buf
    ("(define-sort " ^heap_s^ " () (Array " ^addr_s^ " " ^cell_s^ "))\n")


(* (define-type set     (-> address bool)) *)
let z3_set_preamble buf =
  B.add_string buf
    ("(define-sort " ^set_s^ " () (Array " ^addr_s^ " " ^bool_s^ "))\n")


(* (define-type setth   (-> tid bool))     *)
let z3_setth_preamble buf =
  B.add_string buf
    ("(define-sort " ^setth_s^ " () (Array " ^tid_s^ " " ^bool_s^ "))\n")


let z3_setelem_preamble buf =
  B.add_string buf
    ("(define-sort " ^setelem_s^ " () (Array " ^elem_s^ " " ^bool_s^ "))\n")


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
let z3_path_preamble buf num_addr =
  B.add_string buf
    ( "(define-sort PathLength () " ^int_s^ ")\n" ^
      "(define-fun is_valid_path_length ((i PathLength)) " ^bool_s^
          " (and (<= 0 i) (<= i (+ max_address 1))))\n");
  B.add_string buf
    ( "(define-sort PathAt () (Array RangeAddress " ^addr_s^ "))\n" ^
			"(define-sort PathWhere () (Array " ^addr_s^ " RangeAddress))\n");
	B.add_string buf
		( "(declare-sort " ^path_s^ ")\n" );
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


let z3_unknown_preamble buf =
  B.add_string buf
    ("(declare-sort " ^unk_s^ ")\n")


let z3_pos_preamble buf =
  B.add_string buf ("(define-sort " ^loc_s^ " () " ^int_s^ ")\n");
  GM.sm_decl_fun sort_map pc_name [tid_s] [loc_s] ;
  GM.sm_decl_fun sort_map pc_prime_name [tid_s] [loc_s] ;
	B.add_string buf ("(declare-fun " ^pc_name^ " () (Array " ^tid_s^ " " ^loc_s^ "))\n");
	B.add_string buf ("(declare-fun " ^pc_prime_name^ " () (Array " ^tid_s^ " " ^loc_s^ "))\n");
  B.add_string buf
    (Printf.sprintf "(define-fun in_pos_range ((t %s)) %s\n\
                        (and (<= 1 (select pc t))\n\
                             (<= (select pc t) %i)\n\
                             (<= 1 (select pc_prime t))\n\
                             (<= (select pc_prime t) %i))\n\
                     )\n" tid_s bool_s !prog_lines !prog_lines)


(* (define emptyth::setth)     *)
(*   (lambda (t::tid) (false)) *)
let z3_empth_def buf num_tids =
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


(* (define singletonth::(-> tid setth)   *)
(*     (lambda (t::tid)                  *)
(*         (lambda (r::tid)              *)
(*             (= t r))))                *)
let z3_singletonth_def buf =
  B.add_string buf
    ("(define-fun singletonth ((t " ^tid_s^ ")) " ^setth_s^ "\n" ^
		 "  (store emptyth t true))\n")


(* (define unionth::(-> setth setth setth) *)
(*     (lambda (s::setth r::setth)         *)
(*         (lambda (t::tid)                *)
(*             (or (s t) (r t)))))         *)
let z3_unionth_def buf =
  B.add_string buf
		("(declare-fun unionth (" ^setth_s^ " " ^setth_s^ ") " ^setth_s^ ")\n")


(* (define intersectionth::(-> setth setth setth) *)
(*     (lambda (s::setth r::setth)                *)
(*         (lambda (t::tid)                       *)
(*             (and (s t) (r t)))))               *)
let z3_intersectionth_def buf =
  B.add_string buf
		("(declare-fun intersectionth (" ^setth_s^ " " ^setth_s^ ") " ^setth_s^ ")\n")


(* (define setdiffth::(-> set set set)    *)
(*     (lambda (s::setth r::setth)        *)
(*         (lambda (t::tid)               *)
(*             (and (s t) (not (r t)))))) *)
let z3_setdiffth_def buf =
  B.add_string buf
		("(declare-fun setdiffth (" ^setth_s^ " " ^setth_s^ ") " ^setth_s^ ")\n")


(* (define subseteqth::(-> setth setth bool) *)
(*   (lambda (r::setth) (s::setth)           *)
(*     (and (if (r notid) (s notid))   *)
(*          (if (r t1)       (s t1))         *)
(*          (if (r t2)       (s t2))         *)
(*          (if (r t3)       (s t3)))))      *)
let z3_subseteqth_def buf num_tids =
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


(* (define eqsetth::(-> setth setth bool) *)
let z3_eqsetth_def buf num_tids =
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


(* (define emptyelem::setelem)  *)
(*   (lambda (e::elem) (false)) *)
let z3_empelem_def buf num_elems =
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


(* (define singletonelem::(-> elem setelem)   *)
(*     (lambda (e::elem)                      *)
(*         (lambda (r::elem)                  *)
(*             (= t r))))                     *)
let z3_singletonelem_def buf =
  B.add_string buf
    ("(define-fun singletonelem ((e " ^elem_s^ ")) " ^setelem_s^ "\n" ^
		 "  (store emptyelem e true))\n")


(* (define unionelem::(-> setelem setelem setelem) *)
(*     (lambda (s::setelem r::setelem)             *)
(*         (lambda (e::elem)                       *)
(*             (or (s e) (r e)))))                 *)
let z3_unionelem_def buf =
  B.add_string buf
		("(declare-fun unionelem (" ^setelem_s^ " " ^setelem_s^ ") " ^setelem_s^ ")\n")


(* (define intersectionelem::(-> setelem setelem setelem) *)
(*     (lambda (s::setelem r::setelem)                    *)
(*         (lambda (e::elem)                              *)
(*             (and (s e) (r e)))))                       *)
let z3_intersectionelem_def buf =
  B.add_string buf
		("(declare-fun intersectionelem (" ^setelem_s^ " " ^setelem_s^ ") " ^setelem_s^ ")\n")


(* (define setdiffelem::(-> setelem setelem setelem)    *)
(*     (lambda (s::setelem r::setelem)                  *)
(*         (lambda (e::elem)                            *)
(*             (and (s e) (not (r e))))))               *)
let z3_setdiffelem_def buf =
  B.add_string buf
		("(declare-fun setdiffelem (" ^setelem_s^ " " ^setelem_s^ ") " ^setelem_s^ ")\n")


(* (define subseteqelem::(-> setelem setelem bool) *)
(*   (lambda (r::setelem) (s::setelem)             *)
(*     (and (=> (r e1) (s e1))                     *)
(*          (=> (r e2) (s e2))                     *)
(*          (=> (r e3) (s e3)))))                  *)
let z3_subseteqelem_def buf num_elem =
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


(* (define eqsetelem::(-> setelem setelem bool) *)
let z3_eqsetelem_def buf num_elem =
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


(* (define empty::set)             *)
(*   (lambda (a::address) (false)) *)
let z3_emp_def buf num_addrs =
	let _ = GM.sm_decl_const sort_map "empty" set_s in
	B.add_string buf
		("(declare-fun empty () " ^set_s^ ")\n");
	B.add_string buf
		("(assert (= (select empty null) false))\n");
	for i = 1 to num_addrs do
		B.add_string buf
			("(assert (= (select empty " ^(addr_prefix ^ (string_of_int i))^ ") false))\n")
	done


(* (define singleton::(-> address set)   *)
(*     (lambda (a::address)              *)
(*         (lambda (b::address)          *)
(*             (= a b))))                *)
let z3_singleton_def buf =
  B.add_string buf
    ("(define-fun singleton ((a " ^addr_s^ ")) " ^set_s^ "\n" ^
		 "  (store empty a true))\n")


(* (define setunion::(-> set set set)       *)
(*     (lambda (s::set r::set)            *)
(*         (lambda (a::address)           *)
(*             (or (s a) (r a)))))        *)
let z3_union_def buf =
  B.add_string buf
		("(declare-fun setunion (" ^set_s^ " " ^set_s^ ") " ^set_s^ ")\n")


(* (define intersection::(-> set set set) *)
(*     (lambda (s::set r::set) *)
(*         (lambda (a::address) *)
(*             (and (s a) (r a))))) *)
let z3_intersection_def buf =
  B.add_string buf
	("(declare-fun intersection (" ^set_s^ " " ^set_s^ ") " ^set_s^ ")\n")


(* (define setdiff::(-> set set set)      *)
(*     (lambda (s::set r::set)            *)
(*         (lambda (a::address)           *) 
(*             (and (s a) (not (r a)))))) *)
let z3_setdiff_def buf =
  B.add_string buf
		("(declare-fun setdiff (" ^set_s^ " " ^set_s^ ") " ^set_s^ ")\n")


(* (define subseteq::(-> set set bool)  *)
(*   (lambda (s1::set s2::set)        *)
(*     (and (if (s1 null) (s2 null))    *)
(*          (if (s1 a1) (s2 a1))        *)
(*          (if (s1 a1) (s2 a2))        *)
(*          (if (s1 a3) (s2 a3))        *)
(*          (if (s1 a4) (s2 a4))        *)
(*          (if (s1 a5) (s2 a5)))))     *)
let z3_subseteq_def buf num_addr =
	B.add_string buf
		("(define-fun subseteq ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) "^bool_s^ "\n" ^
		 "  (and (=> (select s1 null) (select s2 null))\n");
	for i = 1 to num_addr do
		let a_str = addr_prefix ^ (string_of_int i) in
		B.add_string buf
			("       (=> (select s1 " ^a_str^ ") (select s2 " ^a_str^ "))\n")
	done;
	B.add_string buf ("))\n")


(* (define eqset::(-> set set bool)  *)
let z3_eqset_def buf num_addr =
	B.add_string buf
		("(define-fun eqset ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) "^bool_s^ "\n" ^
		 "  (and (= (select s1 null) (select s2 null))\n");
	for i = 1 to num_addr do
		let a_str = addr_prefix ^ (string_of_int i) in
		B.add_string buf
			("       (= (select s1 " ^a_str^ ") (select s2 " ^a_str^ "))\n")
	done;
	B.add_string buf ("))\n")


(* (define set2elem::(-> set mem bool)                *)
(*  (lambda (s::set m::mem)                           *)
(*    (lambda (e::elem)                               *)
(*      (or (and (= e (data (m null))) (s null))      *)
(*          (and (= e (data (m aa_1))) (s aa_1))      *)
(*          (and (= e (data (m aa_2))) (s aa_2))      *)
(*          (and (= e (data (m aa_3))) (s aa_3))))))  *)
let z3_settoelems_def buf =
	B.add_string buf
		("(declare-fun set2elem (" ^set_s^ " " ^heap_s^ ") " ^setelem_s^ ")\n")


(* (define getlockat::(-> heap path range_address tid)                *)
(*   (lambda (h::heap p::path i::range_address))                      *)
(*     (lock (h ((select p at) i))))                                  *)
(* (define islockedpos::(-> heap path range_address bool)             *)
(*     (lambda (h::heap p::path i::range_address))                    *)
(*         (and (< i (select p length)) (/= notid (getlockat h p i)))) *)
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
let z3_firstlock_def buf num_addr =
  let strlast = (string_of_int num_addr) in
  B.add_string buf
    ("(define-fun getlockat ((h " ^heap_s^ ") (p " ^path_s^
          ") (i RangeAddress)) " ^tid_s^ "\n" ^
		 "  (if (is_valid_range_address i) (lock (select h (select (at p) i))) notid))\n" ^
     "(define-fun getaddrat ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
     "  (if (is_valid_range_address i) (select (at p) i) null))\n" ^
     "(define-fun islockedpos ((h " ^heap_s^ ") (p " ^path_s^
          ") (i RangeAddress)) " ^bool_s^ "\n" ^
		 "  (if (is_valid_range_address i) (and (< i (length p)) (not (= notid (getlockat h p i)))) false))\n");

  B.add_string buf
    ("(define-fun firstlockfrom" ^ strlast ^ " ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
     "  (if (islockedpos h p " ^ strlast ^ ") (getaddrat p " ^ strlast ^ ") null))\n");
  for i=(num_addr-1) downto 1 do
    let stri    = (string_of_int i) in
    let strnext = (string_of_int (i+1)) in
        B.add_string buf
    ("(define-fun firstlockfrom"^ stri ^" ((h " ^heap_s^ ") (p " ^path_s^ ")) " ^addr_s^ "\n" ^
     "  (if (islockedpos h p "^ stri ^") (getaddrat p "^ stri ^") (firstlockfrom"^ strnext ^" h p)))\n");
  done ;
  B.add_string buf
    ("(define-fun firstlock ((h " ^heap_s^ ") (p " ^path_s^ ") ) " ^addr_s^ "\n" ^
     "  (if (islockedpos h p 0) (getaddrat p 0) (firstlockfrom1 h p)))\n")


(* (define cell_lock::(-> cell tid cell) *)
(*   (lambda (c::cell t::tid)) *)
(*     (mkcell (next c) (data c) t)) *)
let z3_cell_lock buf =
  B.add_string buf
		("(declare-fun cell_lock ((" ^cell_s^ ") (" ^tid_s^ ")) " ^cell_s^ ")\n")


(* (define cell_unlock::(-> cell cell) *)
(*   (lambda (c::cell)) *)
(*     (mkcell (next c) (data c) notid)) *)
let z3_cell_unlock_def buf =
	B.add_string buf
		("(declare-fun cell_unlock ((" ^cell_s^ ") (" ^tid_s^ ")) " ^cell_s^ ")\n")


(* (define epsilonat::(-> range_address address) *)
(*   (lambda r::range_address) null) *)
(* (define epsilonwhere::(-> address range_address) *)
(*   (lambda a::address) 0) *)
(* (define epsilon::path *)
(*    (mk-record length::0 at::epsilonat where::epsilonwhere)) *)

let z3_epsilon_def buf num_addr =
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
let z3_singletonpath_def buf num_addr =
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
		 "  (" ^mkpath_str^ "))\n");
		B.add_string buf
			("(assert (and (= (length (" ^mkpath_str^ ")) 1)\n\
										 (= (at (" ^mkpath_str^ ")) (singletonat a))\n\
										 (= (where (" ^mkpath_str^ ")) (singletonwhere a))\n\
										 (= (addrs (" ^mkpath_str^ ")) (singleton a))))\n")


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
let z3_ispath_def buf num_addr =
  B.add_string buf
    ("(define-fun check_position ((p " ^path_s^ ") (i RangeAddress)) " ^bool_s^ "\n" ^
     "  (=> (and (is_valid_range_address i)\n" ^
     "           (< i (length p)))\n" ^
     "      (= i (select (where p) (select (at p) i)))))\n");
  B.add_string buf
    ("(define-fun ispath ((p " ^path_s^ ")) " ^bool_s^ "\n" ^
     "  (and");
  for i=0 to num_addr do
    B.add_string buf
      ("\n          (check_position p " ^ (string_of_int i) ^ ")")
  done ;
  B.add_string buf "))\n"


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
let z3_rev_def buf num_addr =
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


(* (define path2set::(-> path set)                        *)
(*     (lambda (p::path)                                  *)
(*         (lambda (a::address)                           *)
(*      (< ((select p where) a) (select p length))))) *)
let z3_path2set_def buf =
  B.add_string buf
    ("(define-fun path2set ((p " ^path_s^ ")) " ^set_s^ " (addrs p))\n")


(* (define deref::(-> heap address cell)    *)
(*     (lambda (h::heap a::address)         *)
(*         (h a)))                          *)
let z3_dref_def buf =
  B.add_string buf
    ("(define-fun deref ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^cell_s^ "\n" ^
     "  (select h a))\n")


let z3_elemorder_def buf =
	B.add_string buf
		("(define-fun lesselem ((x " ^elem_s^ ") (y " ^elem_s^ ")) " ^bool_s^ " (< x y))\n" ^
		 "(define-fun greaterelem ((x " ^elem_s^ ") (y " ^elem_s^ ")) " ^bool_s^ " (> x y))\n")


(* Ordered list predicate definition *)
let z3_orderlist_def buf num_addr =
  let idlast = string_of_int num_addr in
  B.add_string buf
    ("(define-fun orderlist" ^idlast^ " ((h " ^heap_s^ ") " ^
     "(a " ^addr_s^ ") (b " ^addr_s^ ")) " ^bool_s^ " \n" ^
     "  true)\n");
  for i = (num_addr-1) downto 1 do
    let id = string_of_int i in
    let idnext = string_of_int (i+1) in
    B.add_string buf
      ("(define-fun orderlist" ^id^ " ((h " ^heap_s^ ") " ^
       "(a " ^addr_s^ ") ( b " ^addr_s^ ")) " ^bool_s^ "\n" ^
       "  (or (= (next" ^id^ " h a) b)\n" ^
			 "      (and (lesselem " ^data ("(select h (next" ^id^ " h a))")^ "\n" ^
			 "                     " ^data ("(select h (next" ^idnext^ " h a))")^ ")\n" ^
			 "           (orderlist" ^idnext^ " h a b))))\n")
  done;
  B.add_string buf
    ("(define-fun orderlist ((h " ^heap_s^ ") " ^
     "(a " ^addr_s^ ") (b " ^addr_s^ ")) " ^bool_s^ "\n" ^
       "  (or (= a b)\n" ^
			 "      (and (lesselem " ^data "(select h a)"^ "\n" ^
			 "                     " ^data "(select h (next1 h a))"^ ")\n" ^
       "           (orderlist1 h a b))))\n")


(* (define error::cell) *)
let z3_error_def buf=
	let _ = GM.sm_decl_const sort_map "error" cell_s in
    B.add_string buf
			("(declare-fun error () " ^cell_s^ ")\n" ^
			 "(assert (= (lock error) notid))\n" ^
       "(assert (= (next error) null))\n")


(* (define mkcell::(-> element address tid cell)        *)
(*     (lambda (h::heap  e::element  a::address k::tid) *)
(*        (mk-record data::e next::a lock::k)))         *)
let z3_mkcell_def buf =
  B.add_string buf
    ("") (* Unneeded *)


(* (define isheap::(-> heap bool)     *)
(*     (lambda (h::heap)              *)
(*         (= (deref h null) error))) *)
let z3_isheap_def buf =
  B.add_string buf
    ("(define-fun isheap ((h " ^heap_s^ ")) " ^bool_s^ "\n" ^
     "  (= (select h null) error))\n")


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
let z3_nextiter_def buf num_addr =
  if (num_addr >= 2) then
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


let z3_reachable_def buf num_addr =
  B.add_string buf
    ("(define-fun isreachable ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^bool_s^ "\n" ^
     "  (or (= from to) (= (next (select h from)) to)\n");
  for i=2 to num_addr do
    B.add_string buf
      ( "\n             (= (next" ^ (string_of_int i)  ^ " h from) to)" )
  done ;
  B.add_string buf "))\n"




(* (define address2set::(-> address set) *)
(*     (lambda (from::address)           *)
(*          (lambda (to::address)        *)
(*              (isreachable from to)))) *)
let z3_address2set_def buf num_addr =
  let join_sets s1 s2 = "\n  (setunion "^ s1 ^" "^ s2 ^")" in
  B.add_string buf
    ("(define-fun address2set ((h " ^heap_s^ ") (from " ^addr_s^ ")) " ^set_s^ "");
  B.add_string buf
    begin
      match num_addr with
        0 -> "\n  (singleton from))\n"
      | 1 -> "\n  (union (singleton from) (singleton (next (select h from)))))\n"
      | _ -> let basic = "\n  (union (singleton from) (singleton (next (select h from))))" in
             let addrs = LeapLib.rangeList 2 num_addr in
             let str   = List.fold_left (fun s i ->
                           join_sets ("(singleton (next"^ (string_of_int i) ^ " h from))") s
                         ) basic addrs
             in
               str^")\n"
		end


(* (define is_singlepath::(-> address path bool) *)
(*     (lambda (a::address p::path)              *)
(*         (and (ispath p)                       *)
(*              (= ((select p length) 1)         *)
(*              (= ((select p at) 0) a)))))      *)
let z3_is_singlepath buf =
  B.add_string buf
    ("(define-fun is_singlepath ((a " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
     "  (and (ispath p)\n" ^
     "       (= (length p) 1)\n" ^
     "       (= (select (at p) 0) a)))\n")
 

(* (define update_heap::(-> heap address cell heap) *)
(*     (lambda (h::heap a::address c::cell)         *)
(*        (update h a c)))                          *)
let z3_update_heap_def buf =
  B.add_string buf
    ("(define-fun update_heap ((h " ^heap_s^ ") (a " ^addr_s^ ") (c " ^cell_s^ ")) " ^heap_s^ "\n" ^
     "  (store h a c))\n")


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
    
let z3_getp_def buf num_addr =
  B.add_string buf
    ("(define-fun update_pathat ((f PathAt) (i RangeAddress) (a " ^addr_s^ ")) PathAt\n" ^
     "  (if (is_valid_range_address i) (store f i a) f))\n" ^
     "(define-fun update_pathwhere ((g PathWhere) (a " ^addr_s^ ") (i RangeAddress)) PathWhere\n" ^
		 "  (if (is_valid_range_address i) (store g a i) g))\n");
(*     "(define-fun add_to_path ((p " ^path_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
		 "  (mkpath (+ 1 (length p))\n" ^
     "          (update_pathat (at p) (length p) a)\n" ^
     "          (update_pathwhere (where p) a (length p))\n" ^
     "          (setunion (addrs p) (singleton a))))\n");
*)
  B.add_string buf
    ("(define-fun path1 ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
     "  (singlepath a))\n");
  for i=2 to (num_addr +1) do
    let stri= string_of_int i in
    let strpre = string_of_int (i-1) in
		let p_str = "(path"^ strpre ^" h a)" in
		let next_str = "(next"^ strpre ^" h a)" in
		let arg1 = "(+ 1 (length " ^p_str^ "))" in
		let arg2 = "(update_pathat (at " ^p_str^ ") (length " ^p_str^ ") " ^next_str^ ")" in
		let arg3 = "(update_pathwhere (where " ^p_str^ ") " ^next_str^ " (length " ^p_str^ "))" in
		let arg4 = "(setunion (addrs " ^p_str^ ") (singleton " ^next_str^ "))" in
		let mkpath_str =  "  mkpath " ^arg1^ "\n" ^
											"					" ^arg2^ "\n" ^
											"					" ^arg3^ "\n" ^
											"					" ^arg4 in
		B.add_string buf
			("(define-fun path"^ stri ^" ((h " ^heap_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
			 "  (" ^mkpath_str^ "))\n");
		B.add_string buf
			("(assert (and (= (length (" ^mkpath_str^ ")) " ^arg1^ ")\n\
										 (= (at (" ^mkpath_str^ ")) " ^arg2^ ")\n\
										 (= (where (" ^mkpath_str^ ")) " ^arg3^ ")\n\
										 (= (addrs (" ^mkpath_str^ ")) " ^arg4^ ")))\n")
	done ;
  B.add_string buf
    ("(define-fun getp"^ (string_of_int (num_addr + 1)) ^" ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
     "  (if (= (next"^ (string_of_int num_addr) ^" h from) to)\n" ^
     "      (path"^ (string_of_int num_addr) ^" h from)\n" ^
     "      epsilon))\n");
  for i=num_addr downto 1 do
    let stri = string_of_int i in
    let strpre = string_of_int (i-1) in
    let strnext = string_of_int (i+1) in
    B.add_string buf
      ("(define-fun getp"^ stri ^" ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (if (= (next"^ strpre ^" h from) to)\n" ^
       "      (path"^ stri ^" h from)\n" ^
       "       (getp"^ strnext ^" h from to)))\n")
  done ;
  B.add_string buf
    ("(define-fun getp ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^path_s^ "\n" ^
     "  (getp1 h from to))\n");
  B.add_string buf
    ("(define-fun isgetp ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
     "  (eqpath p (getp h from to)))\n")


let z3_reach_def buf =
  B.add_string buf
    ( "(define-fun reach ((h " ^heap_s^ ") (from " ^addr_s^ ") " ^
      "(to " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
      "  (and (= (getp h from to) p) (not (= p epsilon))))\n"
    )


(* (define path_length::(-> path range_address) *)
(*     (lambda (p1::path)                       *)
(*         (select p1 length)))                 *)
let z3_path_length_def buf =
  B.add_string buf
    ("(define-fun path_length ((p " ^path_s^ ")) RangeAddress (length p))\n")


(* (define at_path::(-> path range_address address) *)
(*     (lambda (p1::path i::range_address)          *)
(*         ((select p1 at) i)))                     *)
let z3_at_path_def buf =
  B.add_string buf
    ("(define-fun at_path ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
     "  (if (is_valid_range_address i) (select (at p) i) null))\n")


(* (define equal_paths_at::(-> path range_address path range_address bool) *)
(*     (lambda (p1::path i::range_address p2::path j::range_address)       *)
(*         (ite (< i (path_length p1))                                     *)
(*       (= (at_path p1 i) (at_path p2 j))                             *)
(*              true)))                                                    *)
let z3_equal_paths_at_def buf =
  B.add_string buf
    ("(define-fun equal_paths_at ((p1 " ^path_s^ ") (i RangeAddress) (p2 " ^path_s^ ") (j RangeAddress)) " ^bool_s^ "\n" ^
     "  (if (< i (path_length p1))\n" ^
     "      (= (at_path p1 i) (at_path p2 j))\n" ^
     "      true))\n")


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
let z3_is_append_def buf num_addr =
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
let z3_preamble buf num_addr num_tid num_elem req_sorts =
  if (List.exists (fun s ->
        s=Expr.Addr || s=Expr.Cell || s=Expr.Path || s=Expr.Set || s=Expr.Mem
      ) req_sorts) then z3_addr_preamble buf num_addr ;
  if (List.exists (fun s ->
        s=Expr.Thid || s=Expr.Cell || s=Expr.SetTh
      ) req_sorts) then z3_tid_preamble buf num_tid ;
  if (List.exists (fun s ->
        s=Expr.Elem || s=Expr.Cell || s=Expr.Mem
      ) req_sorts) then z3_element_preamble buf num_elem ;
  if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
    z3_cell_preamble buf ;
  if List.mem Expr.Mem     req_sorts then z3_heap_preamble buf ;
  if List.mem Expr.Set     req_sorts then z3_set_preamble buf ;
  if List.mem Expr.SetTh   req_sorts then z3_setth_preamble buf ;
  if List.mem Expr.SetElem req_sorts then z3_setelem_preamble buf ;
  if List.mem Expr.Path    req_sorts then begin
                                            z3_path_preamble buf num_addr ;
                                            z3_ispath_def buf num_addr
                                          end;
  if List.mem Expr.Unknown req_sorts then z3_unknown_preamble buf ;
  z3_pos_preamble buf
  

let z3_defs buf num_addr num_tid num_elem req_sorts req_ops =
  (* Elements *)
  if List.mem Expr.ElemOrder req_ops || List.mem Expr.OrderedList req_ops then
		z3_elemorder_def buf ;
  (* Cells and Heap *)
  if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
    z3_error_def buf ;
  (* Cell *)
  if List.mem Expr.Cell req_sorts then
    begin
      z3_mkcell_def buf ;
      z3_cell_lock buf ;
      z3_cell_unlock_def buf
    end;
  (* Heap *)
  if List.mem Expr.Mem req_sorts then
    begin
      z3_isheap_def buf ;
      z3_dref_def buf ;
      z3_update_heap_def buf
    end;
  (* Sets *)
  if List.mem Expr.Set req_sorts then
    begin
			z3_emp_def buf num_addr ;
      z3_singleton_def buf ;
      z3_union_def buf ;
      z3_intersection_def buf ;
      z3_setdiff_def buf ;
			z3_subseteq_def buf num_addr ;
			z3_eqset_def buf num_addr
		end;
  (* Iterations over next *)
  if List.mem Expr.Addr2Set req_ops || List.mem Expr.OrderedList req_ops then
    z3_nextiter_def buf num_addr ;
  (* Address2set *)
  if List.mem Expr.Addr2Set req_ops then
    begin
      z3_reachable_def buf num_addr ;
      z3_address2set_def buf num_addr
    end;
  (* OrderedList *)
  if List.mem Expr.OrderedList req_ops then z3_orderlist_def buf num_addr ;
  (* Path2set *)
  if List.mem Expr.Path2Set req_ops then z3_path2set_def buf ;
  (* Sets of Threads *)
  if List.mem Expr.SetTh req_sorts then
    begin
			z3_empth_def buf num_tid ;
      z3_singletonth_def buf ;
      z3_unionth_def buf ;
      z3_intersectionth_def buf ;
      z3_setdiffth_def buf ;
			z3_subseteqth_def buf num_tid ;
			z3_eqsetth_def buf num_tid
		end;
  (* Sets of Elements *)
  if List.mem Expr.SetElem req_sorts then
    begin
			z3_empelem_def buf num_elem ;
      z3_singletonelem_def buf ;
      z3_unionelem_def buf ;
      z3_intersectionelem_def buf ;
			z3_setdiffelem_def buf ;
			z3_subseteqelem_def buf num_elem ;
			z3_eqsetelem_def buf num_elem
    end;
  (* Set2Elem *)
	if List.mem Expr.Set2Elem req_ops then z3_settoelems_def buf ;
  (* Firstlock *)
  if List.mem Expr.FstLocked req_ops then z3_firstlock_def buf num_addr ;
  (* Path *)
  if List.mem Expr.Path req_sorts then
    begin
      z3_rev_def buf num_addr ;
			z3_epsilon_def buf num_addr ;
			z3_singletonpath_def buf num_addr ;
      z3_is_singlepath buf ;
      z3_path_length_def buf ;
      z3_at_path_def buf ;
      z3_equal_paths_at_def buf ;
      z3_is_append_def buf num_addr
    end;
  (* Getp *)
  if List.mem Expr.Getp req_ops then z3_getp_def buf num_addr ;
  (* Reachable *)
  if List.mem Expr.Reachable req_ops then z3_reach_def buf

(********************* Preamble Declaration **********************)


let rec z3_define_var (buf:Buffer.t)
                         (tid_set:Expr.VarSet.t)
                         (v:Expr.variable) : unit =
  let (id,s,pr,th,p) = v in
  let sort_str asort = match asort with
                         Expr.Set     -> set_s
                       | Expr.Elem    -> elem_s
                       | Expr.Addr    -> addr_s
                       | Expr.Thid    -> tid_s
                       | Expr.Cell    -> cell_s
                       | Expr.SetTh   -> setth_s
                       | Expr.SetElem -> setelem_s
                       | Expr.Path    -> path_s
                       | Expr.Mem     -> heap_s
                       | Expr.Unknown -> unk_s in
  let s_str = sort_str s in
  let p_id = Option.map_default (fun str -> str ^ "_" ^ id) id p in
  let name = if pr then p_id ^ "_prime" else p_id
  in
    if Expr.is_global_var v then
      begin
        GM.sm_decl_const sort_map name
          (GM.conv_sort (TllInterface.sort_to_expr_sort s)) ;
				B.add_string buf ( "(declare-fun " ^ name ^ " () " ^ s_str ^ ")\n" );
				match s with
				| Expr.Addr -> B.add_string buf ( "(assert (isaddr " ^name^ "))\n" )
				| Expr.Elem -> B.add_string buf ( "(assert (iselem " ^name^ "))\n" )
				| Expr.Path -> B.add_string buf ( "(assert (ispath " ^name^ "))\n" )
				| Expr.Mem  -> B.add_string buf ( "(assert (isheap " ^name^ "))\n" )
				| Expr.Thid ->
(* IMPORTANT: If it doesn't work, put again this line *)
(* let _ = B.add_string buf ( "(assert (not (= " ^ name ^ " notid)))\n" ) in *)
												B.add_string buf ( "(assert (istid " ^name^ "))\n" );
												B.add_string buf ( "(assert (in_pos_range " ^ name ^ "))\n")
				| _    -> ()
      end
    else
      begin
        GM.sm_decl_fun sort_map name [tid_s] [s_str] ;
        B.add_string buf ( "(declare-const " ^ name ^ " (Array " ^tid_s^ " " ^ s_str ^ "))\n" );
        match s with
          Expr.Path -> Expr.VarSet.iter (fun t ->
                    let v_str = variable_invocation_to_str
                                    (Expr.param_var v (Expr.VarTh t)) in
                      B.add_string buf ( "(assert (ispath " ^ v_str ^ "))\n" )
                  ) tid_set
        | Expr.Mem -> Expr.VarSet.iter (fun t ->
                    let v_str = variable_invocation_to_str
                                    (Expr.param_var v (Expr.VarTh t)) in
                      B.add_string buf ( "(assert (isheap " ^ v_str ^ "))\n" )
                  ) tid_set
        | Expr.Thid -> Expr.VarSet.iter (fun t ->
                    let v_str = variable_invocation_to_str
                                    (Expr.param_var v (Expr.VarTh t)) in
											B.add_string buf ( "(assert (not (= " ^ v_str ^ " notid)))\n" )
                  ) tid_set
        | _    -> ()
        (* FIX: Add iterations for ispath and isheap on local variables *)
      end


and define_variables (buf:Buffer.t) (vars:Expr.VarSet.t) : unit =
  let varset     = Expr.varset_of_sort vars Expr.Set  in
  let varelem    = Expr.varset_of_sort vars Expr.Elem in
  let varaddr    = Expr.varset_of_sort vars Expr.Addr in
  let vartid     = Expr.varset_of_sort vars Expr.Thid in
  let varcell    = Expr.varset_of_sort vars Expr.Cell in
  let varsetth   = Expr.varset_of_sort vars Expr.SetTh in
  let varsetelem = Expr.varset_of_sort vars Expr.SetElem in
  let varpath    = Expr.varset_of_sort vars Expr.Path in
  let varmem     = Expr.varset_of_sort vars Expr.Mem  in
  let varunk     = Expr.varset_of_sort vars Expr.Unknown  in
    Expr.VarSet.iter (z3_define_var buf vartid) varset;
    Expr.VarSet.iter (z3_define_var buf vartid) varelem;
    Expr.VarSet.iter (z3_define_var buf vartid) vartid;
    Expr.VarSet.iter (z3_define_var buf vartid) varaddr;
    Expr.VarSet.iter (z3_define_var buf vartid) varcell;
    Expr.VarSet.iter (z3_define_var buf vartid) varsetth;
    Expr.VarSet.iter (z3_define_var buf vartid) varsetelem;
    Expr.VarSet.iter (z3_define_var buf vartid) varpath;
    Expr.VarSet.iter (z3_define_var buf vartid) varmem;
    Expr.VarSet.iter (z3_define_var buf vartid) varunk


and variables_to_z3 (buf:Buffer.t) (expr:Expr.conjunctive_formula) : unit =
  let vars = Expr.get_varset_from_conj expr
  in
    define_variables buf vars


and variables_from_formula_to_z3 (buf:Buffer.t)
                                    (phi:Expr.formula) : unit =
  let vars = Expr.get_varset_from_formula phi
  in
    define_variables buf vars


and variable_invocation_to_str (v:Expr.variable) : string =
  let (id,s,pr,th,p) = v in
  let th_str = Option.map_default tidterm_to_str "" th in
  let p_str  = Option.map_default (fun n -> Printf.sprintf "%s_" n) "" p in
  let pr_str = if pr then "_prime" else ""
  in
    if th = None then
      Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
    else
      Printf.sprintf " (select %s%s%s %s)" p_str id pr_str th_str


and setterm_to_str (s:Expr.set) : string =
  match s with
			Expr.VarSet v				-> variable_invocation_to_str v
		| Expr.EmptySet				-> "empty"
		| Expr.Singl a				-> Printf.sprintf "(singleton %s)" (addrterm_to_str a)
		| Expr.Union(r,s)			-> set_list := s :: !set_list;
														 Printf.sprintf "(setunion %s %s)"
																									(setterm_to_str r)
																									(setterm_to_str s)
		| Expr.Intr(r,s)      -> set_list := s :: !set_list;
														 Printf.sprintf "(intersection %s %s)"
																									(setterm_to_str r)
																									(setterm_to_str s)
		| Expr.Setdiff(r,s)   -> set_list := s :: !set_list;
														 Printf.sprintf "(setdiff %s %s)"
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
	| Expr.NoThid       -> "notid"
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
		| Expr.MkCell(e,a,th) -> cell_list := c :: !cell_list;
														 Printf.sprintf "(mkcell %s %s %s)"
                                      (elemterm_to_str e)
                                      (addrterm_to_str a)
                                      (tidterm_to_str th)
		| Expr.CellLock(c,th) -> cell_list := c :: !cell_list;
														 Printf.sprintf "(cell_lock %s %s)"													
																			(cellterm_to_str c)
                                      (tidterm_to_str th)
		| Expr.CellUnlock c   -> cell_list := c :: !cell_list;
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
		| Expr.UnionTh(rt,st)   -> setth_list := sth :: !setth_list;
															 Printf.sprintf "(unionth %s %s)"
																		(setthterm_to_str rt)
                                    (setthterm_to_str st)
		| Expr.IntrTh(rt,st)    -> setth_list := sth :: !setth_list;
															 Printf.sprintf "(intersectionth %s %s)"
																		(setthterm_to_str rt)
                                    (setthterm_to_str st)
		| Expr.SetdiffTh(rt,st) -> setth_list := sth :: !setth_list;
															 Printf.sprintf "(setdiffth %s %s)"
                                    (setthterm_to_str rt)
                                    (setthterm_to_str st)


and setelemterm_to_str (se:Expr.setelem) : string =
  match se with
      Expr.VarSetElem v       -> variable_invocation_to_str v
    | Expr.EmptySetElem       -> "emptyelem"
    | Expr.SinglElem e        -> Printf.sprintf "(singletonelem %s)"
                                    (elemterm_to_str e)
		| Expr.UnionElem(rt,st)   -> setelem_list := se :: !setelem_list;
																 Printf.sprintf "(unionelem %s %s)"
                                    (setelemterm_to_str rt)
                                    (setelemterm_to_str st)
		| Expr.IntrElem(rt,st)    -> setelem_list := se :: !setelem_list;
																 Printf.sprintf "(intersectionelem %s %s)"
																		(setelemterm_to_str rt)
                                    (setelemterm_to_str st)
		| Expr.SetToElems(s,m)    -> setelem_list := se :: !setelem_list;
																 Printf.sprintf "(set2elem %s %s)"
																		(setterm_to_str s) (memterm_to_str m)
		| Expr.SetdiffElem(rt,st) -> setelem_list := se :: !setelem_list;
																 Printf.sprintf "(setdiffelem %s %s)"
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


let rec varupdate_to_str (v:Expr.variable)
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
  | Expr.ThidT   th        -> tidterm_to_str th
  | Expr.AddrT   a         -> addrterm_to_str a
  | Expr.CellT   c         -> cellterm_to_str c
  | Expr.SetThT sth        -> setthterm_to_str sth
  | Expr.SetElemT se       -> setelemterm_to_str se
  | Expr.PathT   p         -> pathterm_to_str p
  | Expr.MemT  m           -> memterm_to_str m
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


let lesselem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
  Printf.sprintf "(lesselem %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


let greaterelem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
  Printf.sprintf "(greaterelem %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


let eq_to_str (t1:Expr.term) (t2:Expr.term) : string =
  let str_t1 = (term_to_str t1) in
  let str_t2 = (term_to_str t2) in
  match t1 with
		| Expr.PathT _    -> Printf.sprintf "(eqpath %s %s)"		str_t1 str_t2
		| Expr.SetT _	    -> Printf.sprintf "(eqset %s %s)"			str_t1 str_t2
		| Expr.SetThT _	  -> Printf.sprintf "(eqsetth %s %s)"		str_t1 str_t2
		| Expr.SetElemT _	-> Printf.sprintf "(eqsetelem %s %s)" str_t1 str_t2
		| _								-> Printf.sprintf "(= %s %s)"      		str_t1 str_t2


let ineq_to_str (t1:Expr.term) (t2:Expr.term) : string =
  let str_t1 = (term_to_str t1) in
  let str_t2 = (term_to_str t2) in
  match t1 with
      Expr.PathT _ -> Printf.sprintf "(not (eqpath %s %s))" str_t1 str_t2
    | _            -> Printf.sprintf "(not (= %s %s))"            str_t1 str_t2


let pc_to_str (pc:int) (th:Expr.tid option) (pr:bool) : string =
  let pc_str = if pr then pc_prime_name else pc_name
  in
    Printf.sprintf "(= (select %s %s) %s)" pc_str
        (Option.map_default tidterm_to_str "" th) (linenum_to_str pc)


let pcrange_to_str (pc1:int) (pc2:int)
                      (th:Expr.tid option) (pr:bool) : string =
  let pc_str = if pr then pc_prime_name else pc_name in
  let th_str = Option.map_default tidterm_to_str "" th
  in
    Printf.sprintf "(and (<= %s (select %s %s)) (<= (select %s %s) %s))"
     (linenum_to_str pc1) pc_str th_str pc_str th_str (linenum_to_str pc2)


let pcupdate_to_str (pc:int) (th:Expr.tid) : string =
  Printf.sprintf "(= %s (store %s %s %s))"
    pc_prime_name pc_name (tidterm_to_str th) (linenum_to_str pc)


let z3_partition_assumptions (parts:'a Partition.t list) : string =
  let _ = LeapDebug.debug "entering z3_partition_assumptions...\n" in
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
  let to_z3 = formula_to_str in
  match phi with
    Expr.Literal l       -> literal_to_str l
  | Expr.True            -> " true "
  | Expr.False           -> " false "
  | Expr.And (f1,f2)     -> Printf.sprintf "(and %s %s)" (to_z3 f1)
                                                         (to_z3 f2)
  | Expr.Or (f1,f2)      -> Printf.sprintf "(or %s %s)" (to_z3 f1)
                                                        (to_z3 f2)
  | Expr.Not f           -> Printf.sprintf "(not %s)"   (to_z3 f)
  | Expr.Implies (f1,f2) -> Printf.sprintf "(=> %s %s)" (to_z3 f1)
                                                        (to_z3 f2)
  | Expr.Iff (f1,f2)     -> Printf.sprintf "(= %s %s)" (to_z3 f1)
                                                       (to_z3 f2)


let literal_to_z3 (buf:Buffer.t) (lit:Expr.literal) : unit =
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
				("(assert (and (= " ^data ("(cell_lock " ^c_str^ " " ^t_str^ ")")^ " " ^data c_str^ ")\n\
											 (= (next (cell_lock " ^c_str^ " " ^t_str^ ")) (next " ^c_str^ "))\n\
											 (= (lock (cell_lock " ^c_str^ " " ^t_str^ ")) " ^t_str^ ")))\n")
	| Expr.CellUnlock c	->
			let c_str = cellterm_to_str c in
			let notid_str = tidterm_to_str Expr.NoThid in
				("(assert (and (= " ^data ("(cell_unlock " ^c_str^ ")")^ " " ^data c_str^ ")\n\
											 (= (next (cell_unlock " ^c_str^ ")) (next " ^c_str^ "))\n\
											 (= (lock (cell_unlock " ^c_str^ ")) " ^notid_str^ ")))\n")
	| Expr.MkCell (e,a,t) ->
			let e_str = elemterm_to_str e in
			let a_str = addrterm_to_str a in
			let t_str = tidterm_to_str t in
			let mkcell_str = "mkcell " ^e_str^ " " ^a_str^ " " ^t_str in
				("(assert (and (= " ^data ("(" ^mkcell_str^ ")")^ " " ^e_str^ ")\n\
											 (= (next (" ^mkcell_str^ ")) " ^a_str^ ")\n\
											 (= (lock (" ^mkcell_str^ ")) " ^t_str^ ")))\n")
	| _ -> RAISE(UnexpectedCellTerm(Expr.cell_to_str c))


let process_set (max_addrs:int) (s:Expr.set) : string =
	match s with
	| Expr.Union (r,s) ->
			let r_str = setterm_to_str r in
			let s_str = setterm_to_str s in
			let buff_str = ref ("(assert (= (select (setunion " ^r_str^ " " ^s_str^ ") null) (or (select " ^r_str^ " null) (select " ^s_str^ " null))))\n") in
			for i = 1 to max_addrs do
				let ai_str = addr_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (setunion " ^r_str^ " " ^s_str^ ") " ^ai_str^ ") (or (select " ^r_str^ " " ^ai_str^ ") (select " ^s_str^ " " ^ai_str^ "))))\n");
			done;
			!buff_str
	| Expr.Intr (r,s) ->
			let r_str = setterm_to_str r in
			let s_str = setterm_to_str s in
			let buff_str = ref ("(assert (= (select (intersection " ^r_str^ " " ^s_str^ ") null) (and (select " ^r_str^ " null) (select " ^s_str^ " notid))))\n") in
			for i = 1 to max_addrs do
				let ai_str = addr_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (intersection " ^r_str^ " " ^s_str^ ") " ^ai_str^ ") (and (select " ^r_str^ " " ^ai_str^ ") (select " ^s_str^ " " ^ai_str^ "))))\n");
			done;
			!buff_str
	| Expr.Setdiff (r,s) ->
			let r_str = setterm_to_str r in
			let s_str = setterm_to_str s in
			let buff_str = ref ("(assert (= (select (setdiff " ^r_str^ " " ^s_str^ ") null) (and (select " ^r_str^ " null) (not (select " ^s_str^ " null)))))\n") in
			for i = 1 to max_addrs do
				let ai_str = addr_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (setdiff " ^r_str^ " " ^s_str^ ") " ^ai_str^ ") (and (select " ^r_str^ " " ^ai_str^ ") (not (select " ^s_str^ " " ^ai_str^ ")))))\n");
			done;
			!buff_str
	| _ -> RAISE(UnexpectedSetTerm(Expr.set_to_str s))


let process_setth (max_tids:int) (sth:Expr.setth) : string =
	match sth with
	| Expr.UnionTh (r,s) ->
			let r_str = setthterm_to_str r in
			let s_str = setthterm_to_str s in
			let buff_str = ref ("(assert (= (select (unionth " ^r_str^ " " ^s_str^ ") notid) (or (select " ^r_str^ " notid) (select " ^s_str^ " notid))))\n") in
			for i = 1 to max_tids do
				let ti_str = tid_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (unionth " ^r_str^ " " ^s_str^ ") " ^ti_str^ ") (or (select " ^r_str^ " " ^ti_str^ ") (select " ^s_str^ " " ^ti_str^ "))))\n");
			done;
			!buff_str ^ ("(assert (= (select (unionth " ^r_str^ " " ^s_str^ ") tid_witness) (or (select " ^r_str^ " tid_witness) (select " ^s_str^ " tid_witness))))\n")
	| Expr.IntrTh (r,s) ->
			let r_str = setthterm_to_str r in
			let s_str = setthterm_to_str s in
			let buff_str = ref ("(assert (= (select (intersectionth " ^r_str^ " " ^s_str^ ") notid) (and (select " ^r_str^ " notid) (select " ^s_str^ " notid))))\n") in
			for i = 1 to max_tids do
				let ti_str = tid_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (intersectionth " ^r_str^ " " ^s_str^ ") " ^ti_str^ ") (and (select " ^r_str^ " " ^ti_str^ ") (select " ^s_str^ " " ^ti_str^ "))))\n");
			done;
			!buff_str ^ ("(assert (= (select (intersectionth " ^r_str^ " " ^s_str^ ") tid_witness) (and (select " ^r_str^ " tid_witness) (select " ^s_str^ " tid_witness))))\n")
	| Expr.SetdiffTh (r,s) ->
			let r_str = setthterm_to_str r in
			let s_str = setthterm_to_str s in
			let buff_str = ref ("(assert (= (select (setdiffth " ^r_str^ " " ^s_str^ ") notid) (and (select " ^r_str^ " notid) (not (select " ^s_str^ " notid)))))\n") in
			for i = 1 to max_tids do
				let ti_str = tid_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (setdiffth " ^r_str^ " " ^s_str^ ") " ^ti_str^ ") (and (select " ^r_str^ " " ^ti_str^ ") (not (select " ^s_str^ " " ^ti_str^ ")))))\n");
			done;
			!buff_str ^ ("(assert (= (select (setdiffth " ^r_str^ " " ^s_str^ ") tid_witness) (and (select " ^r_str^ " tid_witness) (not (select " ^s_str^ " tid_witness)))))\n")
	| _ -> RAISE(UnexpectedSetthTerm(Expr.setth_to_str sth))


let process_setelem (max_elems:int) (max_addrs:int) (se:Expr.setelem) : string =
	match se with
	| Expr.UnionElem (r,s) ->
			let r_str = setelemterm_to_str r in
			let s_str = setelemterm_to_str s in
			let buff_str = ref
						("(assert (= (select (unionelem " ^r_str^ " " ^s_str^ ") lowestElem) (or (select " ^r_str^ " lowestElem) (select " ^s_str^ " lowestElem))))\n" ^
						 "(assert (= (select (unionelem " ^r_str^ " " ^s_str^ ") highestElem) (or (select " ^r_str^ " highestElem) (select " ^s_str^ " highestElem))))\n") in
			for i = 1 to max_elems do
				let ei_str = elem_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (unionelem " ^r_str^ " " ^s_str^ ") " ^ei_str^ ") (or (select " ^r_str^ " " ^ei_str^ ") (select " ^s_str^ " " ^ei_str^ "))))\n");
			done;
			!buff_str
	| Expr.IntrElem (r,s) ->
			let r_str = setelemterm_to_str r in
			let s_str = setelemterm_to_str s in
			let buff_str = ref
						("(assert (= (select (intersectionelem " ^r_str^ " " ^s_str^ ") lowestElem) (and (select " ^r_str^ " lowestElem) (select " ^s_str^ " lowestElem))))\n" ^
						 "(assert (= (select (intersectionelem " ^r_str^ " " ^s_str^ ") highestElem) (and (select " ^r_str^ " highestElem) (select " ^s_str^ " highestElem))))\n") in
			for i = 1 to max_elems do
				let ei_str = elem_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (intersectionelem " ^r_str^ " " ^s_str^ ") " ^ei_str^ ") (and (select " ^r_str^ " " ^ei_str^ ") (select " ^s_str^ " " ^ei_str^ "))))\n");
			done;
			!buff_str
	| Expr.SetdiffElem (r,s) ->
			let r_str = setelemterm_to_str r in
			let s_str = setelemterm_to_str s in
			let buff_str = ref
						("(assert (= (select (setdiffelem " ^r_str^ " " ^s_str^ ") lowestElem) (and (select " ^r_str^ " lowestElem) (not (select " ^s_str^ " lowestElem)))))\n" ^
						 "(assert (= (select (setdiffelem " ^r_str^ " " ^s_str^ ") highestElem) (and (select " ^r_str^ " highestElem) (not (select " ^s_str^ " highestElem)))))\n") in
			for i = 1 to max_elems do
				let ei_str = elem_prefix ^ (string_of_int i) in
				buff_str := !buff_str ^ ("(assert (= (select (setdiffelem " ^r_str^ " " ^s_str^ ") " ^ei_str^ ") (and (select " ^r_str^ " " ^ei_str^ ") (not (select " ^s_str^ " " ^ei_str^ ")))))\n");
			done;
			!buff_str
	| Expr.SetToElems (s,m) ->
			let s_str = setterm_to_str s in
			let m_str = memterm_to_str m in
			let proc_all_address (e_str:string) : string =
				let buff_str = ref ("(or (not (select (set2elem " ^s_str^ " " ^m_str^ ") " ^e_str^ "))\n" ^
														"    (and (select " ^s_str^ " null) (= " ^data ("(select " ^m_str^ " null)")^ " " ^e_str^ "))\n") in
				for i = 1 to max_addrs do
					let a_str = addr_prefix ^ (string_of_int i) in
					buff_str := !buff_str ^ (" 	  (and (select " ^s_str^ " " ^a_str^ ") (= " ^data ("(select " ^m_str^ " " ^a_str^ ")")^ " " ^e_str^ "))\n")
				done;
				!buff_str ^ (")\n") in
			let buff = ref ("(assert (and \n"^(proc_all_address "lowestElem") ^" " ^(proc_all_address "highestElem")^ "\n") in
			for i = 1 to max_elems do
				let e_str = elem_prefix ^ (string_of_int i) in
				buff := !buff ^ (proc_all_address e_str) ^ "\n"
			done;
			(!buff ^ "))\n")
	| _ -> RAISE(UnexpectedSetelemTerm(Expr.setelem_to_str se))


let literal_list_to_str (ls:Expr.literal list) : string =
	clean_lists();
	let _ = GM.clear_sort_map sort_map in
  let expr = Expr.Conj ls in
	let c = SmpTll.cut_off_normalized expr in
  let num_addr = c.SmpTll.num_addrs in
  let num_tid = c.SmpTll.num_tids in
  let num_elem = c.SmpTll.num_elems in
  let (req_sorts, req_ops) =
    List.fold_left (fun (ss,os) lit ->
      let phi = Expr.Literal lit
      in
        (Expr.required_sorts phi @ ss, Expr.special_ops phi @ os)
    ) ([],[]) ls in
  let buf = B.create 1024 in
      z3_preamble buf num_addr num_tid num_elem req_sorts;
      z3_defs    buf num_addr num_tid num_elem req_sorts req_ops;
      variables_to_z3 buf expr ;
      let add_and_literal l str =
  "\n         " ^ (literal_to_str l) ^ str
      in
      let formula_str = List.fold_right add_and_literal ls ""
      in
	List.iter (process_addr>>(B.add_string buf)) !addr_list;
	List.iter (process_tid>>(B.add_string buf)) !tid_list;
	List.iter (process_elem>>(B.add_string buf)) !elem_list;
	List.iter (process_cell>>(B.add_string buf)) !cell_list;
	List.iter ((process_set num_addr)>>(B.add_string buf)) !set_list;
	List.iter ((process_setth num_tid)>>(B.add_string buf)) !setth_list;
	List.iter ((process_setelem num_elem num_addr)>>(B.add_string buf)) !setelem_list;
  B.add_string buf "(assert\n   (and";
  B.add_string buf formula_str ;
	B.add_string buf "))\n";
	B.add_string buf "(check-sat)\n" ;
	B.contents   buf


let formula_to_str (stac:Tactics.solve_tactic_t option)
                   (co:Smp.cutoff_strategy)
                   (copt:Smp.cutoff_options_t)
									 (phi:Expr.formula) : string =

	LOG "Entering formula_to_str..." LEVEL TRACE;
	let extra_info_str =
    match stac with
    | None -> ""
    | Some Tactics.Cases ->
        let (ante,(eq,ineq)) =
          match phi with
          | Expr.Not (Expr.Implies (ante,cons)) -> (ante, Expr.get_addrs_eqs ante)
          | _ -> (phi, ([],[])) in

        let temp_dom = Expr.TermSet.elements
                        (Expr.termset_of_sort
                          (Expr.get_termset_from_formula ante) Expr.Addr) in

        (* We also filter primed variables *)
        let term_dom = List.filter (fun t ->
                         match t with
                         | Expr.AddrT (Expr.VarAddr (id,s,pr,th,p)) -> th <> None || p = None
                         | _ -> true
                       ) temp_dom in

        let assumps = List.map (fun (x,y) -> Partition.Eq (Expr.AddrT x, Expr.AddrT y)) eq @
                      List.map (fun (x,y) -> Partition.Ineq (Expr.AddrT x, Expr.AddrT y)) ineq in
				verb "**** SMTTllQuery. Domain: %i\n" (List.length term_dom);
				verb "**** SMTTllQuery. Assumptions: %i\n" (List.length assumps);

        let parts = Partition.gen_partitions term_dom assumps in
        let _ = if LeapDebug.is_debug_enabled() then
                  List.iter (fun p ->
										verb "**** SMTTllQuery. Partitions:\n%s\n"
												 (Partition.to_str p Expr.term_to_str);
									) parts in
				verb "**** SMTTllQuery. Number of cases: %i\n" (List.length parts);
				verb "**** SMTTllQuery. Computation done!!!\n";
					z3_partition_assumptions parts in

	clean_lists();
	let _ = GM.clear_sort_map sort_map in
	verb "**** SMTTllQuery. Will compute the cutoff...\n";
	let max_cut_off = SmpTll.cut_off co copt phi in
  let num_addr    = max_cut_off.SmpTll.num_addrs in
  let num_tid     = max_cut_off.SmpTll.num_tids in
	let num_elem    = max_cut_off.SmpTll.num_elems in
  let req_sorts   = Expr.required_sorts phi in
  let req_ops     = Expr.special_ops phi in
  let formula_str = formula_to_str phi in
  let buf         = B.create 1024
  in
    z3_preamble buf num_addr num_tid num_elem req_sorts;
    z3_defs     buf num_addr num_tid num_elem req_sorts req_ops;
    variables_from_formula_to_z3 buf phi ;
    (* We add extra information if needed *)
    B.add_string buf extra_info_str ;
		List.iter (process_addr>>(B.add_string buf)) !addr_list;
		List.iter (process_tid>>(B.add_string buf)) !tid_list;
		List.iter (process_elem>>(B.add_string buf)) !elem_list;
		List.iter (process_cell>>(B.add_string buf)) !cell_list;
		List.iter ((process_set num_addr)>>(B.add_string buf)) !set_list;
		List.iter ((process_setth num_tid)>>(B.add_string buf)) !setth_list;
		List.iter ((process_setelem num_elem num_addr)>>(B.add_string buf)) !setelem_list;
    B.add_string buf "(assert\n";
		B.add_string buf formula_str ;
		B.add_string buf ")\n";
		B.add_string buf "(check-sat)\n" ;
		B.contents   buf


let conjformula_to_str (expr:Expr.conjunctive_formula) : string =
  match expr with
    Expr.TrueConj   -> "(assert true)\n(check-sat)"
  | Expr.FalseConj  -> "(assert false)\n(check-sat)"
  | Expr.Conj conjs -> literal_list_to_str conjs


let get_sort_map () : GM.sort_map_t =
	GM.copy_sort_map sort_map
