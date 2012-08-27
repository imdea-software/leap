module PosExp = PosExpression
module TllExp = TllExpression
module NumExp = NumExpression

module YicesPos : PosSolver.S = PosSolver.Make(BackendSolvers.Yices)
module Z3Pos    : PosSolver.S = PosSolver.Make(BackendSolvers.Z3)

module YicesTll : TllSolver.S = TllSolver.Make(BackendSolvers.Yices)
module Z3Tll    : TllSolver.S = TllSolver.Make(BackendSolvers.Z3)

module YicesNum : NumSolver.S = NumSolver.Make(BackendSolvers.Yices)

let _ = LeapDebug.enable_debug ()

let test = function
  | true  -> "PASS"
  | false -> "FAIL"

let _ =
  Format.printf "Testing Position Solvers...@."; 
  let exp = PosExp.Not PosExp.False in
  begin
    let module S = (val PosSolver.choose "Yices" : PosSolver.S) in
    Printf.printf "Yices : %s\n" (test (S.is_valid 1 exp));
    let module S = (val PosSolver.choose "Z3" : PosSolver.S) in
    Printf.printf "Z3    : %s\n" (test (S.is_valid 1 exp));
  end;
  
  Printf.printf "\n";
  
  Printf.printf "Testing TLL Solvers...\n";
  let exp = TllExp.Not TllExp.False in
  let strat = SmpTll.Dnf in
  begin  
    let module S = (val TllSolver.choose "Yices" : TllSolver.S) in
    Printf.printf "Yices : %s\n" (test (S.is_valid 1 strat exp));
    let module S = (val TllSolver.choose "Z3" : TllSolver.S) in
    Printf.printf "Z3    : %s\n" (test (S.is_valid 1 strat exp));
  end;
  
  Printf.printf "\n";
  
  Printf.printf "Testing Numeric Solvers...\n"; 
  let exp =  NumExp.Not NumExp.False in
  begin
    let module S = (val NumSolver.choose "Yices" : NumSolver.S) in
    Printf.printf "Yices : %s\n" (test (YicesNum.is_valid exp));
  end;

_DEBUG "TEST!";
__DEBUG "CONTINUES!!";
__DEBUG "CONTINUES!!";
_DEBUG "TEST!!!";

_DEBUG_FLUSH_

let f () = (); let s = "Hola\n" in Format.print_string s

let _ = f ()


