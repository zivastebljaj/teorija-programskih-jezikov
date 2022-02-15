let read_source filename =
  let channel = open_in filename in
  let source = really_input_string channel (in_channel_length channel) in
  close_in channel;
  source

let () =
  let source = read_source "test.imp" in
  let cmd = Parser.parse source in
  let _res = Interpreter.eval_cmd [] cmd in
  print_endline "Uspelo mi je!"
