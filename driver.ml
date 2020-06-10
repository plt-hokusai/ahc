module C = import "./compile.ml"
module A = import "./assemble.ml"
module T = import "./tc.ml"
open import "./parser.ml"
open import "prelude.ml"
open import "lua/io.ml"

module Stg = import "./stg/lower.ml"
module Out = import "./stg/output.ml"

external val dofile : string -> () = "dofile"

let printerror (e, { line, col }) =
  put_line @@ "line " ^ show line ^ ", col " ^ show col ^ ":"
  print e

let go infile outfile =
  let infile = open_for_reading infile
  let outfile = open_file outfile Write_m
  match read_all infile with
  | Some str ->
    match lex prog str with
    | Right (ds, _) ->
      ds
        |> T.tc_program [] []
        |> fun (_, _, z) -> z
        |> C.program
        |> A.assm_program
        |> write_bytes outfile
    | Left e -> printerror e
  | _ -> ()
  close_file infile
  close_file outfile

let go' infile outfile =
  go infile outfile
  dofile outfile

let test str =
  match lex prog str with
  | Right (ds, _) ->
      let code =
        ds
          |> T.tc_program [] []
          |> fun (_, _, z) -> z
          |> C.program
      let lua = code |> A.assm_program
      print code
      put_line lua
  | Left e -> printerror e

let test_file infile =
  let infile = open_for_reading infile
  match read_all infile with
  | Some str -> test str
  | None -> ()
  close_file infile

let rec take n xs =
  match n, xs with
  | _, [] -> []
  | 0, _ -> []
  | n, Cons (x, xs) -> Cons (x, take (n - 1) xs)

let go_stg infile outfile =
  let infile = open_for_reading infile
  let outfile = open_file outfile Write_m
  match read_all infile with
  | Some str -> 
    match lex prog str with
    | Right (ds, _) ->
      let decs =
        ds |> T.tc_program [] []
          |> fun (_, _, z) -> z
          |> flip (>>=) Stg.lower_dec
      let (_, sts, locals) = foldl Out.stmts_of_def (M.empty, [], []) decs
      write_bytes outfile "local Constr_mt = { __call = function(x) return x end }\n"
      Out.get_file_contents () |> (^"\n") |> write_bytes outfile
      write_bytes outfile (Out.mk_pap_def ^ "\n")
      write_bytes outfile (Out.ppr_stmt "" (Out.Local (take 100 locals, [])) ^ "\n")
      iter (write_bytes outfile # (^"\n") # Out.ppr_stmt "") sts
      write_bytes outfile "main_entry(function() return 'the real world is fake' end)\n"
    | Left e ->
      printerror e
  | None -> ()
  close_file infile
  close_file outfile

external val args : string * string =
  "{ _1 = select(1, ...), _2 = select(2, ...) }"
external val has_args : bool = "select('#', ...) ~= 0"

let () =
  if has_args then
    let (from, into) = args
    go from into
  else ()
