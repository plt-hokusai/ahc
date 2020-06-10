module Stg = import "./stg.ml"
module Map = import "data/map.ml"
module Set = import "data/set.ml"
module Strings = import "../lib/strings.ml"

open Stg

open import "lua/io.ml"
open import "prelude.ml"

type lua_ref 'expr =
  | Lvar   of string
  | Lindex of lua_ref 'expr * 'expr

type lua_expr 'stmt =
  | Lfunc   of list string * list 'stmt
  | Lcall_e of lua_expr 'stmt * list (lua_expr 'stmt)
  | Lstr    of string
  | Lint    of int
  | Lref    of lua_ref (lua_expr 'stmt)
  | Lbop    of lua_expr 'stmt * string * lua_expr 'stmt
  | Ltable  of list (lua_expr 'stmt * lua_expr 'stmt)
  | Ltrue
  | Ldots

type lua_stmt =
  | Return of lua_expr lua_stmt
  | Local  of list string * list (lua_expr lua_stmt)
  | Func   of string * list string * list lua_stmt
  | Assign of list (lua_ref (lua_expr lua_stmt)) * list (lua_expr lua_stmt)
  | If     of lua_expr lua_stmt * list lua_stmt * list lua_stmt

let rec ppr_ref indl = function
  | Lvar v -> v
  | Lindex (e, Lstr x) -> ppr_ref indl e ^ "." ^ x
  | Lindex (e, e') -> ppr_ref indl e ^ "[" ^ ppr_expr indl e' ^ "]"

and ppr_expr indl = function
  | Lfunc (args, body) ->
    "function(" ^ ppr_args args ^ ")\n" ^ ppr_body (indl ^ "  ") body ^ indl ^ "end"
  | Lcall_e (Lref _ as func, args) ->
    ppr_expr indl func ^ "(" ^ ppr_args (ppr_expr indl <$> args) ^ ")"
  | Lcall_e (func, args) ->
    "(" ^ ppr_expr indl func ^ ")(" ^ ppr_args (ppr_expr indl <$> args) ^ ")"
  | Lstr s -> show s
  | Lint i -> show i
  | Ldots -> "..."
  | Lref r -> ppr_ref indl r
  | Ltrue -> "true"
  | Lbop (l, o, r) -> ppr_expr indl l ^ " " ^ o ^ " " ^ ppr_expr indl r
  | Ltable entries -> "{" ^ ppr_args (ppr_pair indl <$> entries) ^ "}"

and ppr_stmt indl = function
  | Return r -> "return " ^ ppr_expr indl r

  | If (c, t, []) ->
    "if " ^ ppr_expr indl c ^ " then\n"
      ^ ppr_body (indl ^ "  ") t
      ^ indl ^ "end"

  | If (c, [], e) ->
    "if not (" ^ ppr_expr indl c ^ ") then\n"
      ^ ppr_body (indl ^ "  ") e
      ^ indl ^ "end"

  | If (c, t, e) ->
    "if " ^ ppr_expr indl c ^ " then\n"
      ^ ppr_body (indl ^ "  ") t
      ^ indl ^ "else\n"
      ^ ppr_body (indl ^ "  ") e
      ^ indl ^ "end"
  
  | Local ([], []) -> ""
  | Local (vs, []) -> "local " ^ ppr_args vs
  | Local (vs, es) ->
    "local " ^ ppr_args vs ^ " = " ^ ppr_args (ppr_expr indl <$> es)
  | Assign (vs, es) ->
    ppr_args (ppr_ref indl <$> vs) ^ " = " ^ ppr_args (ppr_expr indl <$> es)
  | Func (n, args, body) ->
    "function " ^ n ^ "(" ^ ppr_args args ^ ")\n" ^ ppr_body (indl ^ "  ") body ^ indl ^ "end"

and ppr_args = function
  | [] -> ""
  | Cons (a, args) -> foldl (fun a b -> a ^ ", " ^ b) a args

and ppr_body indl = function
  | [] -> "\n"
  | Cons (a, args) ->
    foldl (fun a b -> a ^ "\n" ^ indl ^ b) (indl ^ ppr_stmt indl a) (ppr_stmt indl <$> args) ^ "\n"

and ppr_pair indl (k, v) = "[" ^ ppr_expr indl k ^ "] = " ^ ppr_expr indl v

let gensym =
  let counter = ref 0
  fun () ->
    counter := !counter + 1
    "_a" ^ show !counter

let escape = function
  | "nil" -> "_Lnil"
  | x -> x

let var x = Lref (Lvar (escape x))

let mk_pap_def =
  "\
local function mk_pap(fun, ...) \
  local pending = { ... }\
  return setmetatable({}, { __call = function(...) \
    local args = table.pack(...)\
    for i = 1, #pending do\
      table.insert(args, i, pending[i])\
    end\
    return fun(unpack(args, 1, args.n + #pending))\
  end}) \
end"

let make_lambda name args body =
  let name = escape name
  let args = map escape args
  let arity = length args
  [ Local ([name, name ^ "_entry" ], []),
    Func (name ^ "_entry", args, body),
    Func (name, ["..."], [
      If (Lbop (Lcall_e (var "select", [Lstr "#", Ldots]), "==", Lint arity), [
        Return (Lcall_e (var (name ^ "_entry"), [Ldots]))
      ], [
        If (Lbop (Lcall_e (var "select", [Lstr "#", Ldots]), ">", Lint arity), [
          Local (["_spill"], [Lcall_e (var "table.pack", [Ldots])]),
          Return (Lcall_e (Lcall_e (var (name ^ "_entry"), [Ldots]),
            [Lcall_e (var "table.unpack", [var "_spill", Lint arity, var "_spill.n"])]))
        ], [
          Return (Lcall_e (var "mk_pap", [var name, Ldots]))
      ])])])]

let expr_of_atom = function
  | Var v -> var v
  | Int i -> Lfunc ([], [Return (Lint i)])

let return x = [Return x]

let rec stmts_of_expr arities = function
  | Atom _ as a  -> expr_of_expr arities a |> return
  | App _ as a   -> expr_of_expr arities a |> return
  | Prim (f, xs) -> stmts_of_prim (f, expr_of_atom <$> xs)
  | Con _ as a   -> expr_of_expr arities a |> return
  | Case (expr, binder, alts) ->
    let rec make_cases = function
      | [] -> [Return (Lcall_e (var "error", [Lstr "Unmatched case"]))]
      | Cons ((Default, tail), _) -> stmts_of_expr arities tail
      | Cons ((Con_pat (tag, names), tail), rest) ->
        let accesses =
          [ Lref (Lindex (Lvar binder, Lint (i + 1)))
          | with i <- [1 .. length names]
          ]
        [If (Lbop (Lref (Lindex (Lvar binder, Lint 1)), "==", Lint tag),
          Local (names, accesses) :: stmts_of_expr arities tail,
          make_cases rest
        )]
    Local ([binder], [enter arities expr]) :: make_cases alts
  | Let (binders, rest) ->
    let names = map (.name) binders
    Local (names, []) :: gen_lambda_forms arities binders ++ stmts_of_expr arities rest

and expr_of_expr arities = function
  | Atom (Var v) ->
    match Map.lookup v arities with
    | Some (Left (0, tag)) -> Lcall_e (var "setmetatable", [ Ltable [(Lint 1, Lint tag)], var "Constr_mt" ])
    | _ -> expr_of_atom (Var v)
  | Atom a -> expr_of_atom a

  | App (f, xs)  ->
    match f with
    | Int _ -> error "Attempt to call int"
    | Var v ->
      match Map.lookup v arities with
      | Some (Right x) when x == length xs ->
        (Lcall_e (var (v ^ "_entry"), expr_of_atom <$> xs))
      | Some (Left (x, tag)) when x == length xs ->
        let go i a = (Lint (i + 1), expr_of_atom a)
        Lcall_e (var "setmetatable", [
          Ltable ((Lint 1, Lint tag) :: zip_with go [1..length xs] xs),
          var "Constr_mt"
        ])
      | _ -> Lcall_e (var v, expr_of_atom <$> xs)

  | Prim (f, xs) -> expr_of_prim (f, expr_of_atom <$> xs)

  | Con (tag, _, atoms) ->
      let go i a = (Lint (i + 1), expr_of_atom a)
      Lcall_e (var "setmetatable", [
        Ltable ((Lint 1, Lint tag) :: zip_with go [1..length atoms] atoms),
        var "Constr_mt"
      ])
    
  | e -> Lcall_e (Lfunc ([], stmts_of_expr arities e), [])

and enter arities expr =
  Lcall_e (expr_of_expr arities expr, [])

and expr_of_prim = function
  | Add, [a, b] -> Lfunc ([], [Return (Lbop (a, "+", b))])
  | Sub, [a, b] -> Lfunc ([], [Return (Lbop (a, "-", b))])
  | Mul, [a, b] -> Lfunc ([], [Return (Lbop (a, "*", b))])
  | Div, [a, b] -> Lfunc ([], [Return (Lbop (a, "/", b))])
  | e -> Lcall_e (Lfunc ([], stmts_of_prim e), [])

and stmts_of_prim = function
  | Equ, [a, b] -> [
      If (Lbop (a, "==", b),
        stmts_of_expr Map.empty (Con (0, 0, [])),
        stmts_of_expr Map.empty (Con (1, 0, [])))
    ]
  | e -> expr_of_prim e |> return

and gen_lambda_forms arities : list (lambda_form stg_expr) -> list lua_stmt = function
  | [] -> []
  | Cons ({update = Function, name, args, body}, rest) ->
    let arities = Map.insert name (Right (length args)) arities
    let bst = stmts_of_expr arities body
    tail (make_lambda name args bst) ++ gen_lambda_forms arities rest
  | Cons ({update = Updatable, name, args, body}, rest) ->
    let body = expr_of_expr arities body
    let s = Assign ([Lvar name], [
      Lcall_e (var "setmetatable", [
        Ltable [],
        Ltable [ (Lstr "__call", Lfunc (["_self"], [
          If (Lref (Lindex (Lvar "_self", Lint 1)), [
            Return (Lref (Lindex (Lvar "_self", Lint 1)))
          ], [
            Local (["val"], [Lcall_e (body, [])]),
            Assign ([Lindex (Lvar "_self", Lint 1)], [var "val"]),
            Return (var "val")
          ])
        ]))
        ]
      ])
    ])
    s :: gen_lambda_forms arities rest

let private pasted_files : ref (Set.t string) = ref Set.empty

let stmts_of_def (arities, code, locals) = function
  | Fun { name, args, body, is_con } ->
    let arities = Map.insert name (match is_con with | Some i -> Left (length args, i) | None -> Right (length args)) arities
    let body = stmts_of_expr arities body
    let Cons (Local (locals', _), def) = make_lambda name args body
    (arities, def ++ code, locals' ++ locals)
  | Ffi_def { name, fent, arity } ->
    let fspec =
      match Strings.split_on " " fent with
      | [file, func] ->
        pasted_files := Set.insert file !pasted_files
        func
      | [func] -> func
      | _ -> error @@ "Foreign spec too big: " ^ fent
    let args = [ gensym () | with _ <- [1 .. arity] ]
    let Cons (Local (locals', _), def) = make_lambda name args [Return (Lcall_e (var fspec, var <$> args))]
    (arities, def ++ code, locals' ++ locals)

let get_file_contents () =
  let files = Set.members !pasted_files
  let go contents path =
    let f = open_for_reading path
    let x = read_all f
    close_file f
    match x with
    | Some s -> "--- foreign file: " ^ path ^ "\n" ^ s ^ "\n" ^ contents
    | None -> contents
  foldl go "" files