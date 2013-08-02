module GenSet = LeapGenericSet

let _ =
  let s1 = GenSet.empty () in
  let s2 = GenSet.empty () in
  GenSet.add s2 "b";
  GenSet.add s1 "a";
  GenSet.add s1 "b";
  GenSet.add s2 "a";
  GenSet.add s2 "c";
  Printf.printf "Sets s1 and s2 are equal: %b\n" (GenSet.equal s1 s2);
  Printf.printf "Set s1 is a subset of s2: %b\n" (GenSet.subseteq s1 s2);

  let a = Hashtbl.create 10 in
  let b = Hashtbl.create 10 in
  Hashtbl.add b 2 "b";
  Hashtbl.add b 1 "a";
  Hashtbl.add a 1 "a";
  Hashtbl.add a 2 "b";
  Printf.printf "Tables a and b are equal: %b\n" (a = b);

  let r1 = GenSet.empty () in
  let r2 = GenSet.empty () in
  GenSet.add r1 "A";
  GenSet.add r1 "B";
  GenSet.add r2 "B";
  GenSet.add r2 "C";
  Printf.printf "Set r1 = %s\n" (GenSet.to_str (fun x -> x) r1);
  Printf.printf "Set r2 = %s\n" (GenSet.to_str (fun x -> x) r2);
  Printf.printf "Set difference r1-r2 = %s\n" (GenSet.to_str (fun x -> x) (GenSet.diff r1 r2))
  

