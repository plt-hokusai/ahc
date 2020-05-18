module C = import "./compile.ml"
module A = import "./assemble.ml"
open import "./parser.ml"
open import "prelude.ml"
open import "lua/io.ml"

let go infile outfile =
  let infile = open_for_reading infile
  let outfile = open_file outfile Write_m
  match read_all infile with
  | Some str ->
    match lex prog str with
    | Right (ds, _) ->
      ds
        |> ds_prog
        |> C.program
        |> A.assm_program
        |> write_bytes outfile
    | Left e -> print e
  | _ -> ()
  close_file infile
  close_file outfile

let test str =
  match lex prog str with
  | Right (ds, _) ->
      ds
        |> ds_prog
        |> C.program
        |> A.assm_program
        |> put_line
  | Left e -> print e

let test_file infile =
  let infile = open_for_reading infile
  match read_all infile with
  | Some str -> test str
  | None -> ()
  close_file infile


external val args : string * string =
  "{ _1 = select(1, ...), _2 = select(2, ...) }"
external val has_args : bool = "select('#', ...) ~= 0"

let () =
  if has_args then
    let (from, into) = args
    go from into
  else ()
