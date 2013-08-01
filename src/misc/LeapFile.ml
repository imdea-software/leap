
let read (filename:string) : string =
  if filename = "" then
    ""
  else begin
    let in_channel = Pervasives.open_in filename in
    let buff = Buffer.create 1024 in
    try
      while true do
        let line = Pervasives.input_line in_channel in
        Buffer.add_string buff (line ^ "\n")
      done; ""
    with End_of_file -> begin
      Pervasives.close_in in_channel;
      Buffer.contents buff
    end
  end
