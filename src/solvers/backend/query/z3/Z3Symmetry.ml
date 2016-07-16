
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




let symmetry (fx:'a -> string)
             (f_spdom: 'b -> string)
             (f_dom:int -> string)
             (xs:'a list)
             (sp_dom:'b list)
             (dom:int) : string =
  if List.length xs > 0 && dom > 0 then begin
    let xs_str = List.map fx xs in
    let sp_dom_str = List.map f_spdom sp_dom in
    
    let (or_assert,_) =
      List.fold_left (fun (str,i) elem ->
        if i < dom then begin
          let sp_dom_assert = List.fold_left (fun str v ->
                                str ^ "(= " ^elem^ " " ^v^ ") "
                              ) "" sp_dom_str in
          let dom_assert = ref "" in
          for j = i downto 1 do
            dom_assert := !dom_assert ^ "(= " ^elem^ " " ^(f_dom j)^ ") "
          done;
          (str ^ "  (or " ^ sp_dom_assert ^ !dom_assert ^ ")\n", i+1)
        end else begin (str, i) end
      ) ("",1) xs_str in
    if or_assert = "" then "" else "(assert (and\n" ^ or_assert ^ "))\n"
  end else
    ""
