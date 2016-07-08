
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



module type CUSTOM_POSSOLVER = sig
  module PosExp : ExpressionTypes.POSEXP
  
  val check_sat   : int -> PosExp.expression -> Sat.t
  val check_valid : int -> PosExp.expression -> Valid.t
end

module type S = CUSTOM_POSSOLVER
  with module PosExp = PosExpression


module Make(Solver : BackendSolverIntf.BACKEND_POS) : S =
struct
  module PosExp = Solver.Translate.Pos.Exp
  
  (* INVOCATIONS *)
  let check_sat (lines : int) (expr : PosExp.expression) : Sat.t =
    let use_smt () =
      (Solver.Translate.Pos.set_prog_lines lines;
       Solver.check_sat (Solver.Translate.Pos.expression expr)) in
    let use_sat () =
      let m = try Hashtbl.find BackendSolvers.posTbl Minisat.Minisat.identifier
              with Not_found -> BackendSolvers.defaultPos () in
      let module SATSolver = (val m : BackendSolverIntf.BACKEND_POS) in
      SATSolver.check_sat (SATSolver.Translate.Pos.expression expr) in

    if PosExp.has_pc expr then
      use_smt()
    else begin
      if Solver.identifier = Minisat.Minisat.identifier then
        use_sat()
      else
        use_smt()
    end


  let check_valid (lines : int) (expr : PosExp.expression) : Valid.t =
(*    LOG "Entering check_valid..." LEVEL TRACE; *)
    Response.sat_to_valid (check_sat lines (PosExpression.Not(expr)))
end


let choose (solverIdent : string) : (module S) =
  let m = try Hashtbl.find BackendSolvers.posTbl solverIdent
    with Not_found -> BackendSolvers.defaultPos () in
  let module Sol = (val m : BackendSolverIntf.BACKEND_POS) in
  (module Make(Sol) : S)
