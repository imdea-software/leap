
open Printf
open LeapLib

module E = Expression

type inv_t = System.var_table_t * Tag.f_tag option * E.formula

type results_t = int * int * int * int * int * int * int * int *
                 int * int * int * int * string

type vc_status = NotVerified | NotValid | IsValid | Unneeded

type status_t = Unverified | Invalid | Valid of DP.t

exception Invalid_folder of string


let table_divider_str =
  "+-----+-----+-----------+-----+-----------+-----+-----------+-----+-----------+-----+-----------+\n"


(* Auxiliary functions *)
let time_to_str (t:float) : string =
  let ints = int_of_float (t /. 10.) in
  let decs = t -. (float_of_int (ints * 10)) in
    if ints = 0 then
      sprintf "     %.3f " decs
    else
      sprintf "%5d%.3f " ints decs


(* Conversion of reports to string *)


let status_to_str (st:status_t) : string =
  match st with
  | Unverified -> "Unverified"
  | Invalid    -> "Invalid"
  | Valid dp   -> "Valid (" ^DP.to_str dp^ ")"


let report_generated_vcs_to_str (vcs:Tactics.vc_info list) (n:int) : string =
  "+- Verification condition generation ---------------------------------\n" ^
  "| Generated vcs:               " ^(string_of_int (List.length vcs))^ "\n" ^
  "| Generated proof obligations: " ^(string_of_int n)^ "\n" ^
  "+- Verification condition generation ---------------------------------\n"


let report_inv_cand_to_str (inv:E.formula) : string =
  let inv_str = E.formula_to_str inv in
  let voc_str = String.concat ", " $ List.map E.tid_to_str (E.voc inv)
  in
  "+- Invariant information ---------------------------------------------\n" ^
  "| Candidate : " ^ inv_str ^ "\n" ^
  "| Vocabulary: " ^ voc_str ^ "\n" ^
  "+---------------------------------------------------------------------\n"


let report_to_str (sys:System.t) : string =
  let sys_str = System.to_str sys
  in
  "-- Program description -----------------------------------------------\n" ^
  sys_str ^
  "----------------------------------------------------------------------\n"



let report_sup_inv_to_str (invs:inv_t list) : string =
  let num = string_of_int (List.length invs) in
  let inv_str = List.fold_left (fun str (s_vars, s_tag, s_inv) ->
                  let phi_str = E.formula_to_str s_inv in
                  let voc_list = System.get_var_id_list s_vars in
                  let voc_str = String.concat ", " voc_list
                  in
                    str ^ "| Inv: " ^ phi_str ^ "\n" ^
                          "| Voc: " ^ voc_str ^ "\n" ^
                          "| \n"
                ) "" invs   
  in
  "+- Supporting invariants: " ^num^ " ------------------------------------------\n" ^
  inv_str


let report_gen_sup_inv_to_str (gen_inv:E.formula) : string =
  let inv_str = E.formula_to_str gen_inv
  in
  "+- Generated supporting invariant ------------------------------------\n" ^
  "| " ^ inv_str ^ "\n" ^
  "+---------------------------------------------------------------------\n"


let report_results_to_str (res:results_t) : string =
  let (total, pos_calls,  pos_sats,
              num_calls,  num_sats,
              tll_calls,  tll_sats,
              tslk_calls, tslk_sats,
              tsl_calls,  tsl_sats,
              remains, file) = res in
  let file_str = 
    if file <> "" then
      "| Output file: " ^ file ^ "\n" ^
      "+---------------------------------------------------------------------\n"
    else ""
  in
  "+- Results -----------------------------------------------------------\n" ^
  file_str ^
  "| Total generated VCs:  " ^ (string_of_int total) ^ "\n" ^
  "| Location DP calls:    " ^ (string_of_int pos_calls) ^ "\n" ^
  "| Location DP verified: " ^ (string_of_int pos_sats) ^ "\n" ^
  "| Numeric DP calls:     " ^ (string_of_int num_calls) ^ "\n" ^
  "| Numeric DP verified:  " ^ (string_of_int num_sats) ^ "\n" ^
  "| TL3 DP calls:         " ^ (string_of_int tll_calls) ^ "\n" ^
  "| TL3 DP verified:      " ^ (string_of_int tll_sats) ^ "\n" ^
  "| TSLK DP calls:        " ^ (string_of_int tslk_calls) ^ "\n" ^
  "| TSLK DP verified:     " ^ (string_of_int tslk_sats) ^ "\n" ^
  "| TSL DP calls:         " ^ (string_of_int tsl_calls) ^ "\n" ^
  "| TSL DP verified:      " ^ (string_of_int tsl_sats) ^ "\n" ^
  "+---------------------------------------------------------------------\n" ^
  "| Remains unverified:   " ^ (string_of_int remains) ^ "\n" ^
  "+---------------------------------------------------------------------\n"


let report_vc_run_header_to_str (unit) : string =
  table_divider_str ^
  "|  ID | Loc |  Time(s)  | Num |  Time(s)  | TL3 |  Time(s)  | TSK |  Time(s)  | TSL |  Time(s)  |\n" ^
  table_divider_str


let report_vc_run_to_str (id:int) (pos_status:vc_status)  (pos_time:float)
                                  (num_status:vc_status)  (num_time:float)
                                  (tll_status:vc_status)  (tll_time:float)
                                  (tslk_status:vc_status) (tslk_time:float)
                                  (tsl_status:vc_status)  (tsl_time:float)
                                  (desc:string) (filename:string) : string =
  let status_to_str st = match st with
                         | NotVerified -> "  ?  "
                         | NotValid    -> "  X  "
                         | IsValid     -> "  √  "
                         | Unneeded    -> "  -  " in
  let id_to_str i = sprintf "%4d " i
  in
    "|" ^ (id_to_str id) ^
    "|" ^ (status_to_str pos_status)  ^ "|" ^ (time_to_str pos_time)  ^
    "|" ^ (status_to_str num_status)  ^ "|" ^ (time_to_str num_time)  ^
    "|" ^ (status_to_str tll_status)  ^ "|" ^ (time_to_str tll_time)  ^
    "|" ^ (status_to_str tslk_status) ^ "|" ^ (time_to_str tslk_time) ^
    "|" ^ (status_to_str tsl_status)  ^ "|" ^ (time_to_str tsl_time)  ^
    "| " ^ (desc) ^ "\n" ^
    table_divider_str


let report_analysis_time_to_str (time:float) : string =
  "| Total analysis time:                                                                "^(time_to_str time)^"|\n" ^
  table_divider_str


let report_details_to_file_to_str (prog_name:string)
                                  (inv_name:string)
                                  (num,trans,vers:int * E.pc_t * int)
                                  (support:Tag.f_tag list)
                                  (sat:bool)
                                  (times:(string * float) list) : string =
  let supp_str = String.concat " " $ List.map Tag.tag_id support in
  let sat_str = if sat then "SAT" else "UNSAT" in
  let times_str = String.concat " :: " $
                    List.map (fun (lbl,tm) ->
                      sprintf "time %s %.3f" lbl tm
                    ) times in
  sprintf "%s :: %s :: %i :: line %i[%i] :: support %s :: %s :: %s"
    prog_name inv_name num trans vers supp_str sat_str times_str


let report_vc_header_to_str (vc_id:int) (vc:Tactics.vc_info) (num_oblig:int) : string =
  "==  VC " ^(string_of_int vc_id)^
  "  =================================================================\n" ^
  (Tactics.vc_info_to_str_simple vc) ^
  "------------------------------------------------------------------------------\n" ^
  " VC # "^ string_of_int vc_id^
  " requires the verification of " ^string_of_int num_oblig^ " proof obligations\n" ^
  "------------------------------------------------------------------------------\n"


let report_vc_tail_to_str (vc_id:int) (*(res_list:E.formula*num_oblig:int)*)  : string =
  "--  VC " ^(string_of_int vc_id)^
  " results  ---------------------------------------------------------\n" ^
(*
  number of proof obligations
  number of unverified proof obligations
  number of invalid proof obligations
  number of valid proof obligations

  fastest proof obligation
  slowest proof obligation
  average solving time for obligation
  total time to verify all proof obligations

  total number of guessed arrangements
  number of calls to each DP
*)
  "============================================================================"


let report_obligation_header_to_str (ob_id:int) (oblig:E.formula) : string =
  "--  Proof obligation " ^string_of_int ob_id^
  " --------------------------------------------------------\n" ^
  (E.formula_to_str oblig) ^ "\n"


let report_obligation_tail_to_str (st:status_t) (time:float) : string =
  Printf.sprintf (" Result: %s\n Time  : %.3f\n") (status_to_str st) (time)


(* Reporting to standard output *)


let report_generated_vcs (vcs:Tactics.vc_info list) (n:int) : unit =
  print_newline(); print_string (report_generated_vcs_to_str vcs n)


let report_inv_cand (inv:E.formula) : unit =
  print_newline(); print_string (report_inv_cand_to_str inv)


let report_system (sys:System.t) : unit =
  print_newline(); print_string (report_to_str sys)


let report_sup_inv (invs:inv_t list) : unit =
  print_newline(); print_string (report_sup_inv_to_str invs)


let report_gen_sup_inv (gen_inv:E.formula) : unit =
  print_string (report_gen_sup_inv_to_str gen_inv)


let report_results (res:results_t) : unit =
  print_newline(); print_string (report_results_to_str res)


let report_vc_run_header (unit) : unit =
  print_newline(); print_string (report_vc_run_header_to_str())


let report_vc_run (id:int) (pos_status:vc_status)  (pos_time:float)
                           (num_status:vc_status)  (num_time:float)
                           (tll_status:vc_status)  (tll_time:float)
                           (tslk_status:vc_status) (tslk_time:float)
                           (tsl_status:vc_status)  (tsl_time:float)
                           (desc:string) (filename:string) : unit =
  print_string (report_vc_run_to_str id pos_status pos_time
                                        num_status num_time
                                        tll_status tll_time
                                        tslk_status tslk_time
                                        tsl_status tsl_time
                                        desc filename);
  flush stdout


let report_analysis_time (time:float) : unit =
  print_string (report_analysis_time_to_str time)


let report_labels_to_str (tbl:System.label_table_t) : string =
  "Defined labels:\n" ^
    (Hashtbl.fold (fun lbl (f,t) str ->
      str ^ (sprintf "%s : [%i;%i]\n" lbl f t)
     ) tbl "")

let report_labels (tbl:System.label_table_t) : unit =
  print_string (report_labels_to_str tbl)

let report_details_to_file (out_folder:string)
                           (prog_name:string)
                           (inv_name:string)
                           (num,trans,vers:int * E.pc_t * int)
                           (support:Tag.f_tag list)
                           (sat:bool)
                           (times:(string * float) list) : unit =
  if out_folder <> "" then
    if Sys.is_directory out_folder then
      let fName = sprintf "%s/%s_%s_%03d_%i"
                    out_folder prog_name inv_name num trans in
      let out = open_out_gen [Open_creat;Open_trunc;Open_wronly] 0o666 fName in
      let _ = output_string out
                (report_details_to_file_to_str prog_name inv_name
                  (num,trans,vers) support sat times) in
      close_out out
    else
      begin
        Interface.Err.msg "Invalid detailed folder" $
          sprintf "Folder \"%s\" is not a valid folder." out_folder;
        raise(Invalid_folder out_folder)
      end


let report_vc_header (vc_id:int) (vc:Tactics.vc_info) (num_oblig:int) : unit =
  print_newline(); print_string (report_vc_header_to_str vc_id vc num_oblig)

  
let report_vc_tail (vc_id:int) : unit =
  print_newline(); print_string (report_vc_tail_to_str vc_id)


let report_obligation_header (ob_id:int) (oblig:E.formula) : unit =
  print_newline(); print_string (report_obligation_header_to_str ob_id oblig)


let report_obligation_tail (status:status_t) (time:float) : unit =
  print_newline(); print_string (report_obligation_tail_to_str status time)
