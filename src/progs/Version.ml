let version_major = 0

let version_minor = 1

let revision = Revision.value

let _enable_ : bool ref = ref false

let show () : unit =
  if !_enable_ then
    let major_str = string_of_int version_major in
    let minor_str = string_of_int version_minor in
    let revision_str = string_of_int revision in
		print_endline ("LEAP version " ^major_str^ "." ^minor_str^ "." ^revision_str)
  else
    ()
