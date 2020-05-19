include import "./compile.ml"
module Strings = import "./lib/strings.ml"
open import "prelude.ml"
open import "lua/io.ml"
open import "./lang.ml"

let resolve_addr = function
  | Combinator n -> n ^ "_combinator"
  | Arg i -> "stack[sp - " ^ show (i + 1) ^ "][3]"
  | Local i -> "stack[sp - " ^ show i ^ "]"
  | Int i -> show i

let rec gm2lua = function
  | Push addr ->
      "  stack[sp + 1] = " ^ resolve_addr addr ^ "; sp = sp + 1"
  | Pop n ->
      "  sp = sp - " ^ show n
  | Update n ->
      let it = "stack[sp - " ^ show (n + 1) ^ "]"
      "  if type(" ^ it ^ ") == 'table' then\n"
        ^ "    " ^ it ^ "[1] = I; " ^ it ^ "[2] = stack[sp]\n"
        ^ "  else " ^ it ^ " = stack[sp] end\n"
        ^ "  sp = sp - 1"
  | Mkap ->
      "  stack[sp - 1] = { A, stack[sp - 1], stack[sp] }; sp = sp - 1"
  | Unwind ->
      "  return unwind(stack, sp)"
  | Eval -> "  stack[sp] = eval(stack, sp)"
  | Add -> "  stack[sp - 1] = stack[sp - 1] + stack[sp]; sp = sp - 1"
  | Sub -> "  stack[sp - 1] = stack[sp - 1] - stack[sp]; sp = sp - 1"
  | Div -> "  stack[sp - 1] = stack[sp - 1] / stack[sp]; sp = sp - 1"
  | Mul -> "  stack[sp - 1] = stack[sp - 1] * stack[sp]; sp = sp - 1"
  | Alloc lim ->
      let rec go acc n =
        if n > 0 then
          go (acc ^ ";\n  stack[sp + " ^ show n ^ "] = {}") (n - 1)
        else
          acc ^ ";  sp = sp + " ^ show lim
      go "--" lim
  | Slide n ->
      "  stack[sp - " ^ show n ^ "] = stack[sp]; sp = sp - " ^ show n
  | Iszero (yes, no) ->
      "  if stack[sp] == 0 then\n"
        ^ foldl (fun x i -> x ^ "  " ^ gm2lua i ^ ";\n") "" yes
        ^ "  else\n"
        ^ foldl (fun x i -> x ^ "  " ^ gm2lua i ^ ";\n") "" no
        ^ "  end"
  | Pack (arity, tag) ->
      let rec go acc i =
        if i > 0 then
          go (acc ^ ", stack[sp - " ^ show (i - 1) ^ "]") (i - 1)
        else
          acc
      let values = go "" arity
      " stack[sp + 1] = {" ^ show tag ^ values ^ "}; sp = sp + 1"
  | Casejump alts ->
      let rec go con = function
        | [] -> " error('unmatched case')"
        | Cons ((arity, code : list _), alts) ->
          (* Where is the constructor? stack[sp], then it moves to
           * stack[sp - 1]. Generally: stack[sp - i], 0 <= i < arity *)
          let rec go_arg i =
            if i < arity then
              "    stack[sp + 1] = stack[sp - " ^ show i ^ "][" ^ show (i + 2) ^ "]; sp = sp + 1;\n"
                ^ go_arg (i + 1)
            else
              foldl (fun x i -> x ^ "  " ^ gm2lua i ^ ";\n") "" code
          "  if stack[sp][1] == " ^ show con ^ " then\n"
            ^ go_arg 0
            ^ "  else"
            ^ go (con + 1) alts
            ^ "  end"
      go 0 alts

let compute_local_set xs =
  let rec go i (s : S.t string) = function
    | Cons (Fd (Fimport {var}), xs) ->
      if i >= 100 then
        s
      else
        go (i + 2) (S.insert (var ^ "_wrapper") (S.insert (var ^ "_combinator") s)) xs
    | Cons (Sc (name, _), xs) ->
      if i >= 100 then
        s
      else
        go (i + 2) (S.insert name (S.insert (name ^ "_combinator") s)) xs
    | Nil -> s
  go 1 S.empty xs

let sc2lua (name, arity, body) =
  let body =
    body
      |> foldl (fun x s -> x ^ "-- " ^ show s ^ "\n" ^ gm2lua s ^ ";\n") (name ^ " = function(stack, sp)\n")
      |> (^ "end")
  let dec =
    name ^ "_combinator = { F, " ^ name ^ ", " ^ show arity ^ ", " ^ show name ^ " };"
  body ^ "\n" ^ dec

let foreign2lua (Fimport { cc, fent = fspec, var, ftype }) =
  let (file, fspec) =
    match Strings.split_on " " fspec with
    | [file, func] -> (Some file, func)
    | [func] -> (None, func)
    | _ -> error @@ "Foreign spec too big: " ^ fspec
  match cc with
  | Prim -> error "primitive definitions are in Gmcode"
  | Lua ->
    let arity = arity ftype
    let args = map (fun i -> ("a" ^ show i, i)) [1..arity]
    let fcall =
      if arity == 0 then
        fspec
      else
        let Cons ((a, _), args) = args
        fspec ^ "(" ^ foldl (fun a (i, _) -> a ^ ", " ^ i) a args ^ ")"
    let wrapper =
      "local function " ^ var ^ "_wrapper(stack, sp)\n"
      ^ foldl (fun x (a, i) -> x ^ "  local " ^ a ^ " = stack[sp - " ^ show i ^ "][3];\n") "" args
      ^ "  stack[sp - " ^ show arity ^ "] = " ^ fcall ^ "\n"
      ^ "  return unwind(stack, sp - " ^ show arity ^ ")\nend"
    let dec =
      var ^ "_combinator = { F, " ^ var ^ "_wrapper, " ^ show arity ^ ", '" ^ fspec ^ "' };"
    let contents =
      match file with
      | Some path -> 
        let f = open_for_reading path
        let x = read_all f
        close_file f
        match x with
        | Some s -> "--- " ^ path ^ "\n" ^ s ^ "\n"
        | None -> ""
      | None -> ""
    contents ^ wrapper ^ "\n" ^ dec

let codegen = function
  | Sc t -> sc2lua t
  | Fd i -> foreign2lua i

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
    let body = foldl (fun x s -> x ^ codegen s ^ "\n") "" decs
    preamble ^ local_decs ^ "\n" ^ body ^ "unwind({{ A, main_combinator, 123 }}, 1)"
