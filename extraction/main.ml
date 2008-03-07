open Unix
open Stal

let string_of_bool b = match b with
  | true -> "Tautology"
  | false -> "Don't know"

let rec i2n = function 0 -> O | n -> (S (i2n (pred n)))
 
let analyze_file channel  =
try
  let lexbuf = Lexing.from_channel channel in
    Hashtbl.clear Lexer.h;
    Lexer.nb_var := 0;
    Parser.main Lexer.token lexbuf
with
      _ -> failwith "syntax error"


let _ =
  let channel = (in_channel_of_descr  ( openfile Sys.argv.(2) [O_RDONLY] 0644 ))
  in
  let e = analyze_file channel in 
  let level = i2n (int_of_string Sys.argv.(1)) in 
  let res = match (run level e) with Quatuor (_,b,_,_) -> b in 
  print_string (string_of_bool res);
  print_newline();
  if res=true then exit 0 else exit 1


