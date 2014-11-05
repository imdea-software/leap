open TllQuery
open LeapLib


module Z3TllQuery : TLL_QUERY =
struct

  module Expr     = TllExpression
  module V        = TllExpression.V
  module VarIdSet = V.VarIdSet
  module VarSet   = V.VarSet
  module B        = Buffer
  module GM       = GenericModel
  module F        = Formula


  (* Configuration *)
  let use_quantifiers : bool ref = ref false

  let prog_lines = ref 0


  let pc_prime_name  : string = Conf.pc_name ^ "_prime"
  let loc_str        : string = "loc_"
  let range_addr_str : string = "rg_addr_"
  let range_tid_str  : string = "rg_tid_"
  let path_len_str   : string = "p_len_"


  let addr_prefix = "aa_"
  let tid_prefix = "tt_"
  let elem_prefix = "ee_"
  let range_prefix = "rr_"


  (* We store tables to add constraints over elements of specific sorts *)
  let elem_tbl = Hashtbl.create 10

  let clean_lists () : unit =
    Hashtbl.clear elem_tbl


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


  (* Configuration *)
  let set_configuration (set_q:bool) : unit =
    use_quantifiers := set_q

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



  (********************** Auxiliary labeling ***********************)
  let aa (i:int) : string =
    addr_prefix ^ (string_of_int i)


  let tt (i:int) : string =
    tid_prefix ^ (string_of_int i)


  let ee (i:int) : string =
    elem_prefix ^ (string_of_int i)


  let rr (i:int) : string =
    range_prefix ^ (string_of_int i)


  (************************* Declarations **************************)

  let rec variable_invocation_to_str (v:Expr.V.t) : string =
    let id = Expr.V.id v in
    let th_str = shared_or_local_to_str (Expr.V.parameter v) in
    let p_str  = match (Expr.V.scope v) with
                 | Expr.V.GlobalScope -> ""
                 | Expr.V.Scope proc -> proc ^ "_" in
    let pr_str = if (Expr.V.is_primed v) then "_prime" else "" in
    match Expr.V.parameter v with
    | Expr.V.Shared  -> Printf.sprintf " %s%s%s%s" p_str id th_str pr_str
    | Expr.V.Local _ -> Printf.sprintf " (select %s%s%s %s)" p_str id pr_str th_str


  and shared_or_local_to_str (th:Expr.V.shared_or_local) : string =
    match th with
    | Expr.V.Shared -> ""
    | Expr.V.Local t -> variable_invocation_to_str t


  and setterm_to_str (s:Expr.set) : string =
    match s with
        Expr.VarSet v -> variable_invocation_to_str v
      | Expr.EmptySet -> "empty"
      | Expr.Singl a  -> Printf.sprintf "(singleton %s)" (addrterm_to_str a)
      | Expr.Union(r,s) -> Printf.sprintf "(setunion %s %s)" (setterm_to_str r)
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
    | Expr.HavocListElem -> "" (* Don't need a representation for this *)
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
      | Expr.CellAt(m,a)     -> Printf.sprintf "(select %s %s)"
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


  (********************** Preamble Declarations ***********************)


  (* (define-type address (scalar null aa_1 aa_2 aa_3 aa_4 aa_5))   *)
  (* (define max_address::int 5)                                    *)
  (* (define-type range_address (subrange 0 max_address))           *)
  let z3_addr_preamble buf num_addr =
  (*
    let range_addr_list = String.concat " " $
                            List.map range_addr_to_str (LeapLib.rangeList 0 num_addr) in
    let path_len_list = String.concat " " $
                          List.map path_len_to_str (LeapLib.rangeList 0 (num_addr+1)) in
  *)

    B.add_string buf
        ( "(declare-const max_address " ^int_s^ ")\n" ^
          "(assert (= max_address " ^ (string_of_int num_addr) ^ "))\n");
    B.add_string buf ("(declare-datatypes () ((" ^addr_s^ " null") ;
    for i = 1 to num_addr do
      B.add_string buf (" " ^ (aa i))
    done ;
    B.add_string buf ")))\n" ;
    (****** NOTE: In case we use integers to represent addresses ******)
  (*
    B.add_string buf ("(define-sort Address () Int)\n") ;
    B.add_string buf ("(declare-const null Address)\n") ;
    B.add_string buf ("(assert (= null 0))\n") ;
  *)
    (****** NOTE: In case we use integers to represent addresses ******)
    GM.sm_decl_const sort_map "max_address" int_s ;
    if !use_quantifiers then begin
      B.add_string buf
        ("(declare-datatypes () ((RangeAddress");
      for i = 0 to num_addr do
        B.add_string buf (" " ^ (rr i))
      done;
      B.add_string buf (")))\n");
      B.add_string buf
        ("(define-fun range_to_int ((n RangeAddress)) Int\n");
      let str = ref (string_of_int num_addr) in
      for i = (num_addr - 1) downto 0 do
        str := "  (ite (= n " ^(rr i)^ ") " ^(string_of_int i)^ " \n" ^(!str)^ ")"
      done;
      B.add_string buf (!str ^ "\n)");
      B.add_string buf
        ("(define-fun int_to_range ((i Int)) RangeAddress\n");
      let str = ref (rr num_addr) in
      for i = (num_addr - 1) downto 0 do
        str := "  (ite (= i " ^(string_of_int i)^ ") " ^(rr i)^ " \n" ^(!str)^ ")"
      done;
      B.add_string buf (!str ^ "\n)");
      B.add_string buf
        ("(define-fun next_range ((n RangeAddress)) RangeAddress\n");
      let str = ref (rr num_addr) in
      for i = (num_addr - 2) downto 0 do
        str := "  (ite (= n " ^(rr i)^ ") " ^(rr (i+1))^ " \n" ^(!str)^ ")"
      done;
      B.add_string buf (!str ^ "\n)")
    end else begin
      B.add_string buf
         ("(define-sort RangeAddress () " ^int_s^ ")\n" ^
          "(define-fun is_valid_range_address ((i RangeAddress)) " ^bool_s^
              " (and (<= 0 i) (<= i max_address)))\n")
    (*
          "(declare-datatypes () ((RangeAddress " ^ range_addr_list ^ ")))\n" ^
          "(declare-datatypes () ((PathLength " ^ path_len_list ^ ")))\n")
    *)
    end


  (* (define-type tid (scalar NoThread t1 t2 t3)) *)
  (* (define max_tid::int 3)                      *)
  (* (define-type range_tid (subrange 0 max_tid)) *)
  let z3_tid_preamble buf num_tids =
  (*
    let tid_list = String.concat " " $
                     List.map range_tid_to_str (LeapLib.rangeList 0 num_tids) in
  *)
    B.add_string buf ("(declare-datatypes () ((" ^tid_s^ " NoThread") ;
    for i = 1 to num_tids do
      B.add_string buf (" " ^ (tt i))
    done ;
    B.add_string buf ")))\n" ;
    B.add_string buf "; I need the line below to prevent an unknown constant error\n";
    GM.sm_decl_const sort_map "tid_witness" tid_s ;
    B.add_string buf ("(declare-const tid_witness " ^tid_s^ ")\n");
    GM.sm_decl_const sort_map "max_tid" int_s ;
    B.add_string buf
      ( "(declare-const max_tid " ^int_s^ ")\n" ^
        "(assert (= max_tid " ^ (string_of_int num_tids) ^ "))\n")
  (*      "(declare-datatypes () ((RangeTid " ^ tid_list ^ ")))\n") *)


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


(*
    B.add_string buf ("(declare-datatypes () ((" ^ elem_s^ " LowestElem HighestElem") ;
    for i = 1 to num_elems do
      B.add_string buf (" " ^ (ee i))
    done ;
    B.add_string buf ")))\n"
*)
  (*  B.add_string buf ("(declare-sort " ^elem_s^ ")\n") *)


  (* (define-type cell (record data::element next::address lock::tid))   *)
  (* (define next::(-> cell address) (lambda (c::cell) (select c next))) *)
  (* (define data::(-> cell element) (lambda (c::cell) (select c data))) *)
  (* (define lock::(-> cell tid)     (lambda (c::cell) (select c lock))) *)
  let z3_cell_preamble buf =
    B.add_string buf
      ( "(declare-datatypes () ((" ^cell_s^ " (mkcell (data " ^elem_s^
        ") (next " ^addr_s^ ") (lock " ^tid_s^ ")))))\n")
  (*
      ("(define-type cell (record data::element next::address lock::tid))\n"   ^
       "(define next::(-> cell address) (lambda (c::cell) (select c next)))\n" ^
       "(define data::(-> cell element) (lambda (c::cell) (select c data)))\n" ^
       "(define lock::(-> cell tid)     (lambda (c::cell) (select c lock)))\n" )
  *)


  (* (define-type heap    (-> address cell)) *)
  let z3_heap_preamble buf =
    B.add_string buf
      ("(define-sort " ^heap_s^ " () (Array " ^addr_s^ " " ^cell_s^ "))\n")
  (*
      "(define-type heap    (-> address cell))\n"
  *)


  (* (define-type set     (-> address bool)) *)
  let z3_set_preamble buf =
    B.add_string buf
      ("(define-sort " ^set_s^ " () (Array " ^addr_s^ " " ^bool_s^ "))\n")
  (*
      "(define-type set     (-> address bool))\n"
  *)


  (* (define-type setth   (-> tid bool))     *)
  let z3_setth_preamble buf =
    B.add_string buf
      ("(define-sort " ^setth_s^ " () (Array " ^tid_s^ " " ^bool_s^ "))\n")
  (*
      "(define-type setth   (-> tid bool))\n"
  *)


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
        "(define-sort PathWhere () (Array " ^addr_s^ " RangeAddress))\n" ^
        "(declare-datatypes () ((" ^path_s^
            " (mkpath (length PathLength) (at PathAt) (where PathWhere) (addrs " ^set_s^
            ")))))\n");
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun eqpath_pos ((p " ^path_s^ ") (r " ^path_s^
              ") (i RangeAddress)) " ^bool_s^ "\n" ^
         "  (=> (and (< (range_to_int i) (length p)) (< (range_to_int i) (length r)))\n" ^
         "      (= (select (at p) i) (select (at r) i))))\n");
      B.add_string buf
        ("(define-fun eqpath ((p " ^path_s^ ") (r " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (= (length p) (length r))\n" ^
         "       (forall ((n RangeAddress)) (eqpath_pos p r n))))\n")
    end else begin
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
    end



  let z3_unknown_preamble buf =
    B.add_string buf
      ("(declare-sort " ^unk_s^ ")\n")


  let z3_pos_preamble buf =
(* No need to define the program counter as now is just a integer variable *)
    B.add_string buf ("(define-sort " ^loc_s^ " () " ^int_s^ ")\n")
(* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)
(*
    GM.sm_decl_fun sort_map Conf.pc_name [tid_s] [loc_s] ;
    GM.sm_decl_fun sort_map pc_prime_name [tid_s] [loc_s] ;
    B.add_string buf ("(declare-const " ^Conf.pc_name^ " (Array " ^tid_s^ " " ^loc_s^ "))\n");
    B.add_string buf ("(declare-const " ^pc_prime_name^ " (Array " ^tid_s^ " " ^loc_s^ "))\n");
    B.add_string buf
      (Printf.sprintf "(define-fun in_pos_range ((t %s)) %s\n\
                          (and (<= 1 (select pc t))\n\
                               (<= (select pc t) %i)\n\
                               (<= 1 (select pc_prime t))\n\
                               (<= (select pc_prime t) %i))\n\
                       )\n" tid_s bool_s !prog_lines !prog_lines)
*)
(* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)


  (* (define subseteq::(-> set set bool)  *)
  (*   (lambda (s1::set s2::set)        *)
  (*     (and (if (s1 null) (s2 null))    *)
  (*          (if (s1 a1) (s2 a1))        *)
  (*          (if (s1 a1) (s2 a2))        *)
  (*          (if (s1 a3) (s2 a3))        *)
  (*          (if (s1 a4) (s2 a4))        *)
  (*          (if (s1 a5) (s2 a5)))))     *)
  let z3_subseteq_def buf num_addr =
  (*
    B.add_string buf
      ("(define-fun subseteq ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^bool_s^ "\n" ^
       "  (and (=> (select s1 null) (select s2 null))");
      for i=1 to num_addr do
        let aa_i = addr_prefix ^ (string_of_int i) in
        B.add_string buf
          ("\n       (=> (select s1 " ^ aa_i ^ ") (select s2 " ^ aa_i ^ "))")
      done ;
      B.add_string buf "))\n"
  *)
    B.add_string buf
      ("(define-fun subseteq ((s1 " ^set_s^ ") (s2 " ^set_s^ ")) " ^bool_s^ "\n\
          (= (intersection s1 s2) s1))\n")


  let z3_nextn_def (buf:B.t) (heaps:VarSet.t) : unit =
    B.add_string buf
      ("(declare-fun next_n (" ^heap_s^ " " ^addr_s^ " RangeAddress " ^addr_s^ ") " ^bool_s^ ")");
    VarSet.iter (fun heap ->
      let h_str = variable_invocation_to_str heap in
      B.add_string buf
        ("(assert (forall ((a " ^addr_s^ "))\n" ^
         "  (next_n " ^h_str^ " a " ^(rr 0)^ " a)))\n" ^
         "(assert (forall ((a " ^addr_s^ ") (b " ^addr_s^ ") (c " ^addr_s^ ") (n RangeAddress))\n" ^
         "  (=> (and (not (= n " ^(rr 0)^ "))\n" ^
         "           (next_n " ^h_str^ " a n b)\n" ^
         "           (= c (next (select " ^h_str^ " b))))\n" ^
         "      (next_n " ^h_str^ " a (next_range n) c))))\n")
    ) heaps



  (* (define singletonth::(-> tid setth)   *)
  (*     (lambda (t::tid)                  *)
  (*         (lambda (r::tid)              *)
  (*             (= t r))))                *)
  let z3_singletonth_def buf =
    B.add_string buf
      ("(define-fun singletonth ((t " ^tid_s^ ")) " ^setth_s^ "\n" ^
       "  (store ((as const " ^setth_s^ ") false) t true))\n")


  (* (define unionth::(-> setth setth setth) *)
  (*     (lambda (s::setth r::setth)         *)
  (*         (lambda (t::tid)                *)
  (*             (or (s t) (r t)))))         *)
  let z3_unionth_def buf =
    B.add_string buf
      ("(define-fun unionth ((s " ^setth_s^ ") (r " ^setth_s^ ")) " ^setth_s^ "\n" ^
       "  ((_ map or) r s))\n")


  (* (define intersectionth::(-> setth setth setth) *)
  (*     (lambda (s::setth r::setth)                *)
  (*         (lambda (t::tid)                       *)
  (*             (and (s t) (r t)))))               *)
  let z3_intersectionth_def buf =
    B.add_string buf
      ("(define-fun intersectionth ((s " ^setth_s^ ") (r " ^setth_s^ ")) " ^setth_s^ "\n" ^
       "  ((_ map and) r s))\n")


  (* (define setdiffth::(-> set set set)    *)
  (*     (lambda (s::setth r::setth)        *)
  (*         (lambda (t::tid)               *)
  (*             (and (s t) (not (r t)))))) *)
  let z3_setdiffth_def buf =
    B.add_string buf
      ("(define-fun setdiffth ((r " ^setth_s^ ") (s " ^setth_s^ ")) " ^setth_s^ "\n" ^
       "  ((_ map and) r ((_ map not) s)))\n")


  (* (define subseteqth::(-> setth setth bool) *)
  (*   (lambda (r::setth) (s::setth)           *)
  (*     (and (if (r NoThread) (s NoThread))   *)
  (*          (if (r t1)       (s t1))         *)
  (*          (if (r t2)       (s t2))         *)
  (*          (if (r t3)       (s t3)))))      *)
  let z3_subseteqth_def buf num_tids =
  (*
    B.add_string buf
      ("(define-fun subseteqth ((r " ^setth_s^ ") (s " ^setth_s^ ")) " ^bool_s^ "\n" ^
       "  (and (=> (select r NoThread) (select s NoThread))\n");
      for i=1 to num_tids do
        let tt_i = tid_prefix ^ (string_of_int i) in
          B.add_string buf
            ("\n       (=> (select r " ^ tt_i ^ ") (select s " ^ tt_i ^ "))")
      done ;
    B.add_string buf "))\n"
  *)
    B.add_string buf
      ("(define-fun subseteqth ((s1 " ^setth_s^ ") (s2 " ^setth_s^ ")) "
          ^bool_s^ "\n\
          (= (intersectionth s1 s2) s1))\n")


  (* (define singletonelem::(-> elem setelem)   *)
  (*     (lambda (e::elem)                      *)
  (*         (lambda (r::elem)                  *)
  (*             (= t r))))                     *)
  let z3_singletonelem_def buf =
    B.add_string buf
      ("(define-fun singletonelem ((e " ^elem_s^ ")) " ^setelem_s^ "\n" ^
       "  (store ((as const " ^setelem_s^ ") false) e true))\n")


  (* (define unionelem::(-> setelem setelem setelem) *)
  (*     (lambda (s::setelem r::setelem)             *)
  (*         (lambda (e::elem)                       *)
  (*             (or (s e) (r e)))))                 *)
  let z3_unionelem_def buf =
    B.add_string buf
      ("(define-fun unionelem ((s " ^setelem_s^ ") (r " ^setelem_s^ ")) "
         ^setelem_s^ "\n" ^
       "  ((_ map or) r s))\n")


  (* (define intersectionelem::(-> setelem setelem setelem) *)
  (*     (lambda (s::setelem r::setelem)                    *)
  (*         (lambda (e::elem)                              *)
  (*             (and (s e) (r e)))))                       *)
  let z3_intersectionelem_def buf =
    B.add_string buf
      ("(define-fun intersectionelem ((s " ^setelem_s^ ") (r " ^setelem_s^ ")) " 
       ^setelem_s^ "\n" ^
       "  ((_ map and) r s))\n")


  (* (define setdiffelem::(-> setelem setelem setelem)    *)
  (*     (lambda (s::setelem r::setelem)                  *)
  (*         (lambda (e::elem)                            *)
  (*             (and (s e) (not (r e))))))               *)
  let z3_setdiffelem_def buf =
    B.add_string buf
      ("(define-fun setdiffelem ((r " ^setelem_s^ ") (s " ^setelem_s^ ")) "
          ^setelem_s^ "\n" ^
       "  ((_ map and) r ((_ map not) s)))\n")


  (* (define subseteqelem::(-> setelem setelem bool) *)
  (*   (lambda (r::setelem) (s::setelem)             *)
  (*     (and (=> (r e1) (s e1))                     *)
  (*          (=> (r e2) (s e2))                     *)
  (*          (=> (r e3) (s e3)))))                  *)
  let z3_subseteqelem_def buf num_elem =
    B.add_string buf
      ("(define-fun subseteqelem ((s1 " ^setelem_s^ ") (s2 " ^setelem_s^ ")) "
          ^bool_s^ "\n\
          (= (intersectionelem s1 s2) s1))\n")


  (* (define empty::set)             *)
  (*   (lambda (a::address) (false)) *)
  let z3_emp_def buf =
    let _ = GM.sm_decl_const sort_map "empty" set_s
    in
      B.add_string buf
        ("(declare-const empty " ^set_s^ ")\n" ^
         "(assert (= empty ((as const " ^set_s^ ") false)))\n")


  (* (define emptyth::setth)     *)
  (*   (lambda (t::tid) (false)) *)
  let z3_empth_def buf =
    let _ = GM.sm_decl_const sort_map "emptyth" setth_s
    in
      B.add_string buf
        ("(declare-const emptyth " ^setth_s^ ")\n" ^
         "(assert (= emptyth ((as const " ^setth_s^ ") false)))\n")


  (* (define emptyelem::setelem)  *)
  (*   (lambda (e::elem) (false)) *)
  let z3_empelem_def buf =
    let _ = GM.sm_decl_const sort_map "emptyelem" setelem_s
    in
      B.add_string buf
        ("(declare-const emptyelem " ^setelem_s^ ")\n" ^
         "(assert (= emptyelem ((as const " ^setelem_s^ ") false)))\n")

   
  (* (define intersection::(-> set set set) *)
  (*     (lambda (s::set r::set) *)
  (*         (lambda (a::address) *)
  (*             (and (s a) (r a))))) *)
  let z3_intersection_def buf =
    B.add_string buf
    ("(define-fun intersection ((s " ^set_s^ ") (r " ^set_s^ ")) " ^set_s^ "\n" ^
     "  ((_ map and) r s))\n")


  (* (define set2elem::(-> set mem bool)                *)
  (*  (lambda (s::set m::mem)                           *)
  (*    (lambda (e::elem)                               *)
  (*      (or (and (= e (data (m null))) (s null))      *)
  (*          (and (= e (data (m aa_1))) (s aa_1))      *)
  (*          (and (= e (data (m aa_2))) (s aa_2))      *)
  (*          (and (= e (data (m aa_3))) (s aa_3))))))  *)
  let z3_settoelems_def buf num_addr =
(*
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun set2elem ((s " ^set_s^ ") (h " ^heap_s^ ") (se " ^setelem_s^ ")) " ^bool_s^ "\n" ^
         "  (forall ((a " ^addr_s^ ")) (= (select s a) (select se (data (select h a))))))\n")
    end else begin
*)
      let str = ref "    (store emptyelem (data (select m null)) (select s null))\n" in
      for i=1 to num_addr do
        str := "  (unionelem\n" ^ !str ^
               "    (store emptyelem (data (select m " ^(aa i)^ ")) (select s " ^(aa i)^ ")))\n"
      done;
      B.add_string buf
      ("(define-fun set2elem ((s " ^set_s^ ") (m " ^heap_s^ ")) " ^setelem_s^
        "\n" ^ !str ^ ")\n")
(*
    end
*)




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
  let z3_firstlock_def buf num_addr =
    let strlast = (string_of_int num_addr) in
    B.add_string buf
      ("(define-fun getlockat ((h " ^heap_s^ ") (p " ^path_s^
            ") (i RangeAddress)) " ^tid_s^ "\n" ^
       "  (if (is_valid_range_address i) (lock (select h (select (at p) i))) NoThread))\n" ^
       "(define-fun getaddrat ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
       "  (if (is_valid_range_address i) (select (at p) i) null))\n" ^
       "(define-fun islockedpos ((h " ^heap_s^ ") (p " ^path_s^
            ") (i RangeAddress)) " ^bool_s^ "\n" ^
       "  (if (is_valid_range_address i) (and (< i (length p)) (not (= NoThread (getlockat h p i)))) false))\n");

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
      ("(define-fun cell_lock ((c " ^cell_s^ ") (t " ^tid_s^ ")) " ^cell_s^ "\n" ^
       "  (mkcell (data c) (next c) t))\n")


  (* (define cell_unlock::(-> cell cell) *)
  (*   (lambda (c::cell)) *)
  (*     (mkcell (next c) (data c) NoThread)) *)
  let z3_cell_unlock_def buf =
    B.add_string buf
      ("(define-fun cell_unlock ((c " ^cell_s^ ")) " ^cell_s^ "\n" ^
       "  (mkcell (data c) (next c) NoThread))\n")


  (* (define epsilonat::(-> range_address address) *)
  (*   (lambda r::range_address) null) *)
  (* (define epsilonwhere::(-> address range_address) *)
  (*   (lambda a::address) 0) *)
  (* (define epsilon::path *)
  (*    (mk-record length::0 at::epsilonat where::epsilonwhere)) *)

  let z3_epsilon_def buf =
    let _ = GM.sm_decl_const sort_map "epsilon" path_s
    in
      B.add_string buf
        ("(declare-const epsilonat PathAt)\n" ^
         "(assert (= epsilonat ((as const PathAt) null)))\n" ^
         "(declare-const epsilonwhere PathWhere)\n");
      if !use_quantifiers then
        B.add_string buf
          ("(assert (= epsilonwhere ((as const PathWhere) rr_0)))\n")
      else
        B.add_string buf
          ("(assert (= epsilonwhere ((as const PathWhere) 0)))\n");
      B.add_string buf
          ("(declare-const epsilon " ^path_s^ ")\n" ^
           "(assert (= epsilon (mkpath 0 epsilonat epsilonwhere empty)))\n")


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
  let z3_singletonpath_def buf =
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun singletonat ((a " ^addr_s^ ")) PathAt\n" ^
         "  (store ((as const (PathAt)) null) rr_0 a))\n" ^
         "(define-fun singletonwhere ((a " ^addr_s^ ")) PathWhere\n" ^
         "  (store ((as const (PathWhere)) rr_1) a rr_0))\n")
    end else begin
      B.add_string buf
        ("(define-fun singletonat ((a " ^addr_s^ ")) PathAt\n" ^
         "  (store ((as const (PathAt)) null) 0 a))\n" ^
         "(define-fun singletonwhere ((a " ^addr_s^ ")) PathWhere\n" ^
         "  (store ((as const (PathWhere)) 1) a 0))\n")
    end;
    B.add_string buf
      ("(define-fun singlepath ((a " ^addr_s^ ")) " ^path_s^ "\n" ^
       "  (mkpath 1 (singletonat a) (singletonwhere a) (singleton a)))\n")


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
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun addr_in_path ((p " ^path_s^ ") (i RangeAddress)) " ^set_s^ "\n" ^
         "  (ite (and (<= 0 (range_to_int i)) (<= (range_to_int i) (length p)))\n" ^
         "       (store ((as const " ^set_s^ ") false) (select (at p) i) true)\n" ^
         "       ((as const " ^set_s^ ") false)))\n");
      B.add_string buf
        ("(define-fun check_position ((p " ^path_s^ ") (i RangeAddress)) " ^bool_s^ "\n" ^
         "  (ite (< (range_to_int i) (length p))\n" ^
         "       (and (= i (select (where p) (select (at p) i)))\n" ^
         "            (select (addrs p) (select (at p) i)))\n" ^
         "       (not (select (addrs p) (select (at p) i)))))\n");
      B.add_string buf
        ("(define-fun ispath ((p " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (forall ((n RangeAddress)) (check_position p n))\n" ^
         "       (forall ((a Address)) (= (select (addrs p) a)\n" ^
         "                                (and (<= 0 (range_to_int (select (where p) a)))\n" ^
         "                                     (<= (range_to_int (select (where p) a)) (length p)))))))\n")
    end else begin
      let str = ref "empty" in
      for i=0 to num_addr do
        str := "(setunion \n                            " ^
                !str ^ "\n                               (addr_in_path p " ^string_of_int i^ "))"
      done;
      B.add_string buf
        ("(define-fun addr_in_path ((p " ^path_s^ ") (i RangeAddress)) " ^set_s^ "\n" ^
         "  (ite (and (<= 0 i) (<= i (length p)))\n" ^
         "       (singleton (select (at p) i))\n" ^
         "       empty))\n");
      B.add_string buf
        ("(define-fun check_position ((p " ^path_s^ ") (i RangeAddress)) " ^bool_s^ "\n" ^
         "  (ite (and (is_valid_range_address i)\n" ^
         "           (< i (length p)))\n" ^
         "       (and (= i (select (where p) (select (at p) i)))\n" ^
         "            (select (addrs p) (select (at p) i)))\n" ^
         "       (not (select (addrs p) (select (at p) i)))))\n");
      B.add_string buf
        ("(define-fun ispath ((p " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and");
      for i=0 to num_addr do
        B.add_string buf
          ("\n          (and (check_position p " ^ (string_of_int i) ^ ")\n" ^
           "               (= (addrs p) " ^ !str ^ "))\n")
      done ;
      B.add_string buf "))\n"
    end


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
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun rev_position ((p " ^path_s^ ") (p_rev " ^path_s^ ") (n RangeAddress)) " ^bool_s^ "\n" ^
         "  (=> (< (range_to_int n) (length p))\n" ^
         "      (= (select (at p) n) (select (at p_rev) (int_to_range (- (length p) (range_to_int n)))))))\n" ^
         "(define-fun rev ((p " ^path_s^ ") (p_rev " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (= (length p)\n" ^
         "          (length p_rev))\n" ^
         "       (forall ((n RangeAddress)) (rev_position p p_rev n))))\n")
    end else begin
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
      end


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


  let z3_elemorder_def buf num_elem =
    ()
(*
    B.add_string buf ("(declare-fun lesselem (" ^elem_s^ " " ^elem_s^ ") " ^bool_s^ ")\n") ;
    B.add_string buf ("(define-fun greaterelem ((x " ^elem_s^ ") (y " ^elem_s^ ")) " ^bool_s^ "\n" ^
                      "  (lesselem y x))\n") ;
    (* Totality and no-reflexibility *)
    B.add_string buf ("(assert (not (lesselem LowestElem LowestElem)))\n");
    B.add_string buf ("(assert (not (lesselem HighestElem HighestElem)))\n");
    B.add_string buf ("(assert (lesselem LowestElem HighestElem))\n");
    for i = 1 to num_elem do
      let x = ee i  in
      B.add_string buf ("(assert (not (lesselem " ^x^ " " ^x^ ")))\n") ;
      B.add_string buf ("(assert (lesselem LowestElem " ^x^ "))\n");
      B.add_string buf ("(assert (lesselem " ^x^ " HighestElem))\n");
      for j = i+1 to num_elem do
        let y = ee j in
          B.add_string buf ("(assert (or (lesselem " ^x^ " " ^y^ ") (lesselem " ^y^ " " ^x^ ")))\n")
      done
    done ;
    (* TOFIX: Replace buffer in order to prevent segmentation fault due to
              buffer overflow when too many elements are required. *)
    (* Transitivity *)
    let name_elem (i:int) = if (i = 0) then "LowestElem"
                            else if (i = num_elem + 1) then "HighestElem"
                            else ee i in
    for i = 0 to (num_elem + 1) do
      for j = 0 to (num_elem + 1) do
        for k = 0 to (num_elem + 1) do
          if (i<>j && j<>k (*&& i<>k*)) then
            let x = name_elem i in
            let y = name_elem j in
            let z = name_elem k in
            B.add_string buf ("(assert (=> (and (lesselem " ^x^ " " ^y^ ") \
                                                (lesselem " ^y^ " " ^z^ ")) \
                                                (lesselem " ^x^ " " ^z^ ")))\n")
        done
      done
    done
*)


  (* Ordered list predicate definition *)
  let z3_orderlist_def buf num_addr =
(*
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun ordered ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (forall ((n RangeAddress))\n" ^
         "    (=> (<= (range_to_int n) (length p))\n" ^
         "        (=> (< (range_to_int n) (length p))\n" ^
         "            (< (data (select h (select (at p) n)))\n" ^
         "               (data (select h (select (at p) (next_range n)))))))))\n" ^
         "(define-fun orderlist ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^bool_s^ "\n" ^
         "  (ordered h from to (getp h from to)))\n")
    end else begin
*)
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
           "      (and (< (data (select h (next" ^id^ " h a)))\n" ^
           "              (data (select h (next" ^idnext^ " h a))))\n" ^
           "           (orderlist" ^idnext^ " h a b))))\n")
      done;
      B.add_string buf
        ("(define-fun orderlist ((h " ^heap_s^ ") " ^
         "(a " ^addr_s^ ") (b " ^addr_s^ ")) " ^bool_s^ "\n" ^
           "  (or (= a b)\n" ^
           "      (and (< (data (select h a))\n" ^
           "              (data (select h (next1 h a))))\n" ^
           "           (orderlist1 h a b))))\n")
(*
    end
*)


  (* (define error::cell) *)
  let z3_error_def buf=
    let _ = GM.sm_decl_const sort_map "error" cell_s
    in
      B.add_string buf
        ("(declare-const error " ^cell_s^ ")\n" ^
         "(assert (= (lock error) NoThread))\n" ^
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
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun isreachable ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^bool_s^ "\n" ^
          "  (or (= from to)\n" ^
          "      (exists ((n RangeAddress)) (next_n h from n to))))\n")
    end else begin
      B.add_string buf
        ("(define-fun isreachable ((h " ^heap_s^ ") (from " ^addr_s^ ") (to " ^addr_s^ ")) " ^bool_s^ "\n" ^
         "  (or (= from to) (= (next (select h from)) to)\n");
      for i=2 to num_addr do
        B.add_string buf
          ( "\n             (= (next" ^ (string_of_int i)  ^ " h from) to)" )
      done ;
      B.add_string buf "))\n"
    end




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
        | 1 -> "\n  (setunion (singleton from) (singleton (next (select h from)))))\n"
        | _ -> let basic = "\n  (setunion (singleton from) (singleton (next (select h from))))" in
               let addrs = LeapLib.rangeList 2 num_addr in
               let str   = List.fold_left (fun s i ->
                             join_sets ("(singleton (next"^ (string_of_int i) ^ " h from))") s
                           ) basic addrs
               in
                 str^")\n"
      end


  (* (define singleton::(-> address set)   *)
  (*     (lambda (a::address)              *)
  (*         (lambda (b::address)          *)
  (*             (= a b))))                *)
  let z3_singleton_def buf =
    B.add_string buf
      ("(define-fun singleton ((a " ^addr_s^ ")) " ^set_s^ "\n" ^
       "  (store ((as const " ^set_s^ ") false) a true))\n")


  (* (define setunion::(-> set set set)       *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::address)           *)
  (*             (or (s a) (r a)))))        *)
  let z3_union_def buf =
    B.add_string buf
      ("(define-fun setunion ((s " ^set_s^ ") (r " ^set_s^ ")) " ^set_s^ "\n" ^
       "  ((_ map or) r s))\n")


  (* (define setdiff::(-> set set set)      *)
  (*     (lambda (s::set r::set)            *)
  (*         (lambda (a::address)           *) 
  (*             (and (s a) (not (r a)))))) *)
  let z3_setdiff_def buf =
    B.add_string buf
      ("(define-fun setdiff ((r " ^set_s^ ") (s " ^set_s^ ")) " ^set_s^ "\n" ^
       "  ((_ map and) r ((_ map not) s)))\n")


  (* (define is_singlepath::(-> address path bool) *)
  (*     (lambda (a::address p::path)              *)
  (*         (and (ispath p)                       *)
  (*              (= ((select p length) 1)         *)
  (*              (= ((select p at) 0) a)))))      *)
  let z3_is_singlepath buf =
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun is_singlepath ((a " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (ispath p)\n" ^
         "       (= (length p) 1)\n" ^
         "       (= (select (at p) rr_0) a)))\n")
    end else begin
      B.add_string buf
        ("(define-fun is_singlepath ((a " ^addr_s^ ") (p " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (ispath p)\n" ^
         "       (= (length p) 1)\n" ^
         "       (= (select (at p) 0) a)))\n")
    end
   

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
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun update_pathat ((f PathAt) (i RangeAddress) (a " ^addr_s^ ")) PathAt\n" ^
         "  (store f i a))\n" ^
         "(define-fun update_pathwhere ((g PathWhere) (a " ^addr_s^ ") (i RangeAddress)) PathWhere\n" ^
         "  (store g a i))\n" ^
         "(define-fun add_to_path ((p " ^path_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
         "  (mkpath (+ 1 (length p))\n" ^
         "          (update_pathat (at p) (int_to_range (length p)) a)\n" ^
         "          (update_pathwhere (where p) a (int_to_range (length p)))\n" ^
         "          (setunion (addrs p) (singleton a))))\n")
    end else begin
      B.add_string buf
        ("(define-fun update_pathat ((f PathAt) (i RangeAddress) (a " ^addr_s^ ")) PathAt\n" ^
         "  (if (is_valid_range_address i) (store f i a) f))\n" ^
         "(define-fun update_pathwhere ((g PathWhere) (a " ^addr_s^ ") (i RangeAddress)) PathWhere\n" ^
         "  (if (is_valid_range_address i) (store g a i) g))\n" ^
         "(define-fun add_to_path ((p " ^path_s^ ") (a " ^addr_s^ ")) " ^path_s^ "\n" ^
         "  (mkpath (+ 1 (length p))\n" ^
         "          (update_pathat (at p) (length p) a)\n" ^
         "          (update_pathwhere (where p) a (length p))\n" ^
         "          (setunion (addrs p) (singleton a))))\n")
    end;
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
      ("(define-fun path_length ((p " ^path_s^ ")) PathLength (length p))\n")


  (* (define at_path::(-> path range_address address) *)
  (*     (lambda (p1::path i::range_address)          *)
  (*         ((select p1 at) i)))                     *)
  let z3_at_path_def buf =
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun at_path ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
         "  (select (at p) i))\n")
    end else begin
      B.add_string buf
        ("(define-fun at_path ((p " ^path_s^ ") (i RangeAddress)) " ^addr_s^ "\n" ^
         "  (if (is_valid_range_address i) (select (at p) i) null))\n")
    end


  (* (define equal_paths_at::(-> path range_address path range_address bool) *)
  (*     (lambda (p1::path i::range_address p2::path j::range_address)       *)
  (*         (ite (< i (path_length p1))                                     *)
  (*       (= (at_path p1 i) (at_path p2 j))                             *)
  (*              true)))                                                    *)
  let z3_equal_paths_at_def buf =
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun equal_paths_at ((p1 " ^path_s^ ") (i RangeAddress) (p2 " ^path_s^ ") (j RangeAddress)) " ^bool_s^ "\n" ^
         "  (if (< (range_to_int i) (path_length p1))\n" ^
         "      (= (at_path p1 i) (at_path p2 j))\n" ^
         "      true))\n")
    end else begin
      B.add_string buf
        ("(define-fun equal_paths_at ((p1 " ^path_s^ ") (i RangeAddress) (p2 " ^path_s^ ") (j RangeAddress)) " ^bool_s^ "\n" ^
         "  (if (< i (path_length p1))\n" ^
         "      (= (at_path p1 i) (at_path p2 j))\n" ^
         "      true))\n")
    end


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
    if !use_quantifiers then begin
      B.add_string buf
        ("(define-fun is_append ((p1 " ^path_s^ ") (p2 " ^path_s^ ") (p_res " ^path_s^ ")) " ^bool_s^ "\n" ^
         "  (and (= (+ (path_length p1) (path_length p2)) (path_length p_res))\n" ^
         "       (<= (path_length p_res) (+ max_address 1))\n" ^
         "       (forall ((n RangeAddress)) (and (equal_paths_at p1 n p_res n)\n" ^
         "                                       (equal_paths_at p2 n p_res (int_to_range (+ (path_length p1) (range_to_int n))))))))\n")
    end else begin
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
    end


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
  if !use_quantifiers then begin
    if (List.mem Expr.OrderedList req_ops) then begin
      res_req_sorts := Expr.Path :: !res_req_sorts;
      res_req_ops := Expr.Getp :: !res_req_ops;
    end
  end;
  (!res_req_sorts, !res_req_ops)


  let z3_preamble buf num_addr num_tid num_elem req_sorts =
    B.add_string buf ";; TLL Z3 Translation\n";
    if (List.exists (fun s ->
          s=Expr.Addr || s=Expr.Cell || s=Expr.Path || s=Expr.Set || s=Expr.Mem
        ) req_sorts) then z3_addr_preamble buf num_addr ;
    if (List.exists (fun s ->
          s=Expr.Tid || s=Expr.Cell || s=Expr.SetTh || s=Expr.Mem
        ) req_sorts) then z3_tid_preamble buf num_tid ;
    if (List.exists (fun s ->
          s=Expr.Elem || s=Expr.Cell || s=Expr.Mem || s=Expr.SetElem
        ) req_sorts) then z3_element_preamble buf num_elem ;
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      z3_cell_preamble buf ;
    if List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts then
      z3_heap_preamble buf ;
    if List.mem Expr.Set     req_sorts then z3_set_preamble buf ;
    if List.mem Expr.SetTh   req_sorts then z3_setth_preamble buf ;
    if List.mem Expr.SetElem req_sorts then z3_setelem_preamble buf ;
    if List.mem Expr.Path    req_sorts then begin
                                              z3_path_preamble buf num_addr ;
                                              z3_ispath_def buf num_addr
                                            end;
    if List.mem Expr.Unknown req_sorts then z3_unknown_preamble buf ;
    z3_pos_preamble buf



  (********************* Variable Definitions **********************)

  let rec z3_define_var (buf:Buffer.t)
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
    let name = if Expr.V.is_primed v then p_id ^ "_prime" else p_id
    in
      if Expr.V.is_global v then
        begin
          GM.sm_decl_const sort_map name
            (GM.conv_sort (TllInterface.sort_to_expr_sort s)) ;
          B.add_string buf ( "(declare-const " ^ name ^ " " ^ s_str ^ ")\n" );
          match s with
            Expr.Path -> B.add_string buf ( "(assert (ispath " ^ name ^ "))\n" )
          | Expr.Mem  -> B.add_string buf ( "(assert (isheap " ^ name ^ "))\n" )
          | Expr.Elem -> B.add_string buf ( "(assert (iselem " ^ name ^ "))\n" )
          | Expr.Tid -> B.add_string buf ( "(assert (not (= " ^ name ^ " NoThread)))\n" )
(* Since variables and PC are flat into variables, there's no need of pc and pc_prime as arrays *)
(*                         B.add_string buf ( "(assert (in_pos_range " ^ name ^ "))\n") *)
          | _    -> ()
        end
      else
        begin
          GM.sm_decl_fun sort_map name [tid_s] [s_str] ;
          B.add_string buf ( "(declare-const " ^ name ^ " (Array " ^tid_s^ " " ^ s_str ^ "))\n" );
          match s with
          | Expr.Elem -> B.add_string buf ("(assert (iselem (select " ^name^ " NoThread)))\n");
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
                        B.add_string buf ( "(assert (not (= " ^ v_str ^ " NoThread)))\n" )
                    ) tid_set
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
    let varbool    = V.varset_of_sort vars Expr.Bool in
    let varunk     = V.varset_of_sort vars Expr.Unknown  in
      VarSet.iter (z3_define_var buf vartid num_tids) varset;
      VarSet.iter (z3_define_var buf vartid num_tids) varelem;
      VarSet.iter (z3_define_var buf vartid num_tids) vartid;
      VarSet.iter (z3_define_var buf vartid num_tids) varaddr;
      VarSet.iter (z3_define_var buf vartid num_tids) varcell;
      VarSet.iter (z3_define_var buf vartid num_tids) varsetth;
      VarSet.iter (z3_define_var buf vartid num_tids) varsetelem;
      VarSet.iter (z3_define_var buf vartid num_tids) varpath;
      if (not !use_quantifiers) then
        VarSet.iter (z3_define_var buf vartid num_tids) varmem;
      VarSet.iter (z3_define_var buf vartid num_tids) varint;
      VarSet.iter (z3_define_var buf vartid num_tids) varbool;
      VarSet.iter (z3_define_var buf vartid num_tids) varunk


  and variables_to_z3 (buf:Buffer.t)
                      (num_tids:int)
                      (expr:Expr.conjunctive_formula) : unit =
    let vars = Expr.get_varset_from_conj expr
    in
      define_variables buf num_tids vars


  and variables_from_formula_to_z3 (buf:Buffer.t)
                                   (num_tids:int)
                                   (phi:Expr.formula) : unit =
    let vars = Expr.get_varset_from_formula phi
    in
      define_variables buf num_tids vars


  (********************* Preamble Definitions **********************)

  let z3_defs buf num_addr num_tid num_elem req_sorts req_ops heaps =
    (* Elements *)
    if List.mem Expr.ElemOrder req_ops || List.mem Expr.OrderedList req_ops then
      z3_elemorder_def buf num_elem ;
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
        z3_emp_def buf ;
        z3_singleton_def buf ;
        z3_union_def buf ;
        z3_intersection_def buf ;
        z3_setdiff_def buf ;
        z3_subseteq_def buf num_addr
      end;
    (* If quantification is used, then we need to declare the heaps at this point *)
    if (List.mem Expr.Cell req_sorts || List.mem Expr.Mem req_sorts) &&
        !use_quantifiers then
      begin
        VarSet.iter (z3_define_var buf VarSet.empty num_tid) heaps;
        z3_nextn_def buf heaps
      end;
    (* Iterations over next *)
    if List.mem Expr.Addr2Set req_ops
        || List.mem Expr.OrderedList req_ops
        || List.mem Expr.Getp req_ops then
      z3_nextiter_def buf num_addr ;
    (* Address2set *)
    if List.mem Expr.Addr2Set req_ops then
      begin
        z3_reachable_def buf num_addr ;
        z3_address2set_def buf num_addr
      end;
    (* Path2set *)
    if List.mem Expr.Path2Set req_ops then z3_path2set_def buf ;
    (* Sets of Threads *)
    if List.mem Expr.SetTh req_sorts then
      begin
        z3_empth_def buf ;
        z3_singletonth_def buf ;
        z3_unionth_def buf ;
        z3_intersectionth_def buf ;
        z3_setdiffth_def buf ;
        z3_subseteqth_def buf num_tid
      end;
    (* Sets of Elements *)
    if List.mem Expr.SetElem req_sorts then
      begin
        z3_empelem_def buf ;
        z3_singletonelem_def buf ;
        z3_unionelem_def buf ;
        z3_intersectionelem_def buf ;
        z3_setdiffelem_def buf ;
        z3_subseteqelem_def buf num_elem
      end;
    (* Set2Elem *)
    if List.mem Expr.Set2Elem req_ops then z3_settoelems_def buf num_addr ;
    (* Firstlock *)
    if List.mem Expr.FstLocked req_ops then z3_firstlock_def buf num_addr ;
    (* Path *)
    if List.mem Expr.Path req_sorts then
      begin
        z3_rev_def buf num_addr ;
        z3_epsilon_def buf ;
        z3_singletonpath_def buf ;
        z3_is_singlepath buf ;
        z3_path_length_def buf ;
        z3_at_path_def buf ;
        z3_equal_paths_at_def buf ;
        z3_is_append_def buf num_addr
      end;
    (* Getp *)
    if List.mem Expr.Getp req_ops then z3_getp_def buf num_addr ;
    (* OrderedList *)
    if List.mem Expr.OrderedList req_ops then z3_orderlist_def buf num_addr ;
    (* Reachable *)
    if List.mem Expr.Reachable req_ops then z3_reach_def buf

  (********************* Preamble Declaration **********************)


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
    Printf.sprintf "(< %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


  let greaterelem_to_str (e1:Expr.elem) (e2:Expr.elem) : string =
    Printf.sprintf "(> %s %s)" (elemterm_to_str e1) (elemterm_to_str e2)


  let eq_to_str (t1:Expr.term) (t2:Expr.term) : string =
    let str_t1 = (term_to_str t1) in
    let str_t2 = (term_to_str t2) in
    match (t1,t2) with
      | (Expr.PathT _, _) -> "(eqpath " ^str_t1^ " " ^str_t2^ ")"
(*
      | (Expr.SetElemT se, Expr.SetElemT (Expr.SetToElems(s,m)))
      | (Expr.SetElemT (Expr.SetToElems(s,m)), Expr.SetElemT se) ->
          if !use_quantifiers then
            "(set2elem " ^(setterm_to_str s)^ " " ^
                          (memterm_to_str m)^ " " ^
                          (setelemterm_to_str se)^ ")"
          else

            "(= " ^str_t1^ " " ^str_t2^ ")"
*)
      | _ -> "(= " ^str_t1^ " " ^str_t2^ ")"


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
                                   (aa (!counter))
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
    let to_z3 = formula_to_str in
    match phi with
      F.Literal l       -> literal_to_str l
    | F.True            -> " true "
    | F.False           -> " false "
    | F.And (f1,f2)     -> Printf.sprintf "(and %s %s)" (to_z3 f1)
                                                           (to_z3 f2)
    | F.Or (f1,f2)      -> Printf.sprintf "(or %s %s)" (to_z3 f1)
                                                          (to_z3 f2)
    | F.Not f           -> Printf.sprintf "(not %s)"   (to_z3 f)
    | F.Implies (f1,f2) -> Printf.sprintf "(=> %s %s)" (to_z3 f1)
                                                          (to_z3 f2)
    | F.Iff (f1,f2)     -> Printf.sprintf "(= %s %s)" (to_z3 f1)
                                                         (to_z3 f2)


  let literal_to_z3 (buf:Buffer.t) (lit:Expr.literal) : unit =
    B.add_string buf (literal_to_str lit)


  let process_elem (e_expr:string) : string =
    ("(assert (iselem (data " ^e_expr^ ")))\n")


  let post_process (buf:B.t) (num_addrs:int) (num_elems:int) (num_tids:int) : unit =
    Hashtbl.iter (fun e _ -> B.add_string buf (process_elem e)) elem_tbl


  let literal_list_to_str (use_q:bool) (ls:Expr.literal list) : string =
    clean_lists();
    set_configuration use_q;
    GM.clear_sort_map sort_map;
    let expr = F.Conj ls in
    let c = SmpTll.cut_off_normalized expr in
    let num_addr = c.SmpTll.num_addrs in
    let num_tid = c.SmpTll.num_tids in
    let num_elem = c.SmpTll.num_elems in
    let (req_sorts, req_ops) =
      List.fold_left (fun (ss,os) lit ->
        let phi = F.Literal lit
        in
          (Expr.required_sorts phi @ ss, Expr.special_ops phi @ os)
      ) ([],[]) ls in
    let phi_var_tbl = if !use_quantifiers then
                        let set = List.fold_left (fun vs lit ->
                                    VarSet.union vs (Expr.get_varset_from_literal lit)
                                  ) VarSet.empty ls in
                        V.split_by_sort set
                      else
                        Hashtbl.create 1 in
    let heaps       = V.find_in_table_sort phi_var_tbl Expr.Mem in
    let (req_sorts, req_ops) = update_requirements req_sorts req_ops in
    let buf = B.create 1024 in
        z3_preamble buf num_addr num_tid num_elem req_sorts;
        z3_defs    buf num_addr num_tid num_elem req_sorts req_ops heaps;
        variables_to_z3 buf num_tid expr ;
        let add_and_literal l str =
    "\n         " ^ (literal_to_str l) ^ str
        in
        let formula_str = List.fold_right add_and_literal ls ""
        in
    post_process buf num_addr num_elem num_tid;
    B.add_string buf ("(push)\n");
    B.add_string buf "(assert\n   (and";
    B.add_string buf formula_str ;
    B.add_string buf "))\n(check-sat)" ;
    B.contents   buf


  let formula_to_str (co:Smp.cutoff_strategy_t)
                     (copt:Smp.cutoff_options_t)
                     (use_q:bool)
                     (phi:Expr.formula) : string =
    clean_lists();
    set_configuration use_q;
    let _ = LeapDebug.debug "entering Z3TllQuery.formula_to_str...\n" in
    let _ = GM.clear_sort_map sort_map in
    let _ = LeapDebug.debug "Z3TllQuery will compute the cutoff...\n" in
    let max_cut_off = SmpTll.cut_off co copt phi in
    let num_addr    = max_cut_off.SmpTll.num_addrs in
    let num_tid     = max_cut_off.SmpTll.num_tids in
    let num_elem    = max_cut_off.SmpTll.num_elems in
    let req_sorts   = Expr.required_sorts phi in
    let req_ops     = Expr.special_ops phi in
    let phi_var_tbl = if !use_quantifiers then
                        V.split_by_sort (Expr.get_varset_from_formula phi)
                      else
                        Hashtbl.create 1 in
    let heaps       = V.find_in_table_sort phi_var_tbl Expr.Mem in
    let (req_sorts, req_ops) = update_requirements req_sorts req_ops in
    let formula_str = formula_to_str phi in
    let buf         = B.create 1024
    in
      B.add_string buf (";; Translation for " ^ (Expr.formula_to_str phi) ^ "\n");
      z3_preamble buf num_addr num_tid num_elem req_sorts;
      z3_defs     buf num_addr num_tid num_elem req_sorts req_ops heaps;
      variables_from_formula_to_z3 buf num_tid phi ;
      (* We add extra information if needed *)
(*      B.add_string buf extra_info_str ; *)
      post_process buf num_addr num_elem num_tid;

      (* Use symmetry over addresses *)
      if !use_quantifiers then begin
        let addr_vars = VarSet.elements (V.find_in_table_sort phi_var_tbl 
        Expr.Addr) in
        B.add_string buf
          (Z3Symmetry.symmetry variable_invocation_to_str addrterm_to_str aa
                        addr_vars [Expr.Null] num_addr)
      end;

      B.add_string buf ("(push)\n");
      B.add_string buf "(assert\n";
      B.add_string buf formula_str ;
      B.add_string buf ")\n(check-sat)" ;
      LeapDebug.debug "exiting Z3TllQuery.formula_to_str...\n";
      B.contents   buf


  let conjformula_to_str (use_q:bool) (expr:Expr.conjunctive_formula) : string =
    match expr with
      F.TrueConj   -> "(assert true)\n(check-sat)"
    | F.FalseConj  -> "(assert false)\n(check-sat)"
    | F.Conj conjs -> literal_list_to_str use_q conjs


  let get_sort_map () : GM.sort_map_t =
    GM.copy_sort_map sort_map

end
