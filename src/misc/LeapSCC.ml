
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



module GenSet = LeapGenericSet

type 'a graph_info_t =
  {
            codom   : 'a GenSet.t ;
    mutable index   : int         ;
    mutable lowlink : int         ;
  }


let tarjan (g:('a,'a graph_info_t) Hashtbl.t) : 'a list list =
  let index = ref 0 in
  let s = ref [] in
  let res = ref [] in

  let rec strongconnect (v:'a) : unit =
    begin
      let v_info = Hashtbl.find g v in
      v_info.index <- !index;
      v_info.lowlink <- !index;
      incr index;
      s := v :: !s;
      GenSet.iter (fun w ->
        let w_info = Hashtbl.find g w in
        if w_info.index = -1 then
          (strongconnect w; v_info.lowlink <- min v_info.lowlink w_info.lowlink)
        else if List.mem w !s then
          v_info.lowlink <- min v_info.lowlink w_info.index
      ) v_info.codom;
      if v_info.lowlink = v_info.index then begin
        let (preds,succs) = LeapLib.split_at !s v in
        s := succs;
        res := preds :: !res
      end
    end

  in
    Hashtbl.iter (fun v info ->
      if info.index = -1 then
        strongconnect v
    ) g;
    !res


let scc (graph:('a,'a GenSet.t) Hashtbl.t) : 'a list list =
  (* ALE: Load all necessary information in graph g, which will be the one
     used for the computations. *)
  let graph_dom = Hashtbl.fold (fun e s d_set ->
                    GenSet.add d_set e; GenSet.union s d_set
                  ) graph (GenSet.empty ()) in
  let g : ('a,'a graph_info_t) Hashtbl.t =
    Hashtbl.create (GenSet.size graph_dom) in
  GenSet.iter (fun e ->
    let codom = try Hashtbl.find graph e with _ -> GenSet.empty () in
    Hashtbl.add g e {codom = codom; index = -1; lowlink = -1;}
  ) graph_dom;
  let res = tarjan g in
  res


let has_cycles (graph:('a,'a GenSet.t) Hashtbl.t) : bool =
  List.exists (fun sc -> List.length sc > 1) (scc graph)

