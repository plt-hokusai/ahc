include import "./compile.ml"
open import "prelude.ml"
open import "lua/io.ml"

let resolve_addr = function
  | Combinator n -> n ^ "_combinator"
  | Arg i -> "stack[sp - " ^ show (i + 1) ^ "][3]"

let gm2lua = function
  | Push addr -> "  stack[sp + 1] = " ^ resolve_addr addr ^ "; sp = sp + 1"
  | Pop n -> "  sp = sp - " ^ show n
  | Update n -> "  stack[sp - " ^ show (n + 1) ^ "] = { I, stack[sp] }; sp = sp - 1"
  | Mkap -> "  stack[sp - 1] = { A, stack[sp - 1], stack[sp] }; sp = sp - 1"
  | Unwind -> "  return unwind()"

let compute_local_set xs =
  let rec go i (s : S.t string) = function
    | Cons ((name, _, _), xs) ->
      if i >= 100 then
        s
      else
        go (i + 2) (S.insert name (S.insert (name ^ "_combinator") s)) xs
    | Nil -> s
  go 1 S.empty xs

let sc2lua (name, arity, body) =
  let body =
    body
      |> foldl (fun x s -> x ^ gm2lua s ^ ";\n") (name ^ " = function()\n")
      |> (^ "end")
  let dec =
    name ^ "_combinator = { F, " ^ name ^ ", " ^ show arity ^ ", " ^ show name ^ " };"
  body ^ "\n" ^ dec

let preamble =
  let f = open_for_reading "preamble.lua"
  let x = read_all f
  close_file f
  match x with
  | Some s -> s
  | None -> error "no preamble.lua"

let assm_program decs =
  match decs with
  | [] -> error "empty program"
  | _ ->
    let Cons (local1, locals) =
      compute_local_set decs |> S.members
    let local_decs =
      foldl (fun x v -> x ^ ", " ^ v) ("local " ^ local1) locals
    let body = foldl (fun x s -> x ^ sc2lua s ^ "\n") "" decs
    preamble ^ local_decs ^ "\n" ^ body ^ "stack[sp] = { A, main_combinator, 0 }; unwind()"
