module GenSet = LeapGenericSet

let _ =
  let s1 = GenSet.empty () in
  let s2 = GenSet.empty () in
  GenSet.add s2 "b";
  GenSet.add s1 "a";
  GenSet.add s1 "b";
  GenSet.add s2 "a";
  Printf.printf "Sets s1 and s2 are equal: %b\n" (GenSet.equal s1 s2);

  let a = Hashtbl.create 10 in
  let b = Hashtbl.create 10 in
  Hashtbl.add b 2 "b";
  Hashtbl.add b 1 "a";
  Hashtbl.add a 1 "a";
  Hashtbl.add a 2 "b";
  Printf.printf "Tables a and b are equal: %b\n" (a = b)

