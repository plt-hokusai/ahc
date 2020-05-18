module M = import "data/map.ml"
module S = import "data/set.ml"

open import "prelude.ml"
open import "./lang.ml"
open import "./lib/monads.ml"

type addr =
  | Combinator of string
  | Arg of int
  | Int of int

type gm_code =
  | Push of addr
  | Update of int
  | Pop of int
  | Unwind
  | Mkap
  | Add | Sub | Mul | Div | Eval
  | Iszero of list gm_code * list gm_code

instance show gm_code begin
  let show = function
    | Mkap -> "Mkap"
    | Unwind -> "Unwind"
    | Push (Combinator k) -> "Push " ^ k
    | Push (Arg i) -> "Arg " ^ show i
    | Push (Int i) -> "Int " ^ show i
    | Update n -> "Update " ^ show n
    | Pop n -> "Pop " ^ show n
    | Add  -> "Add"
    | Mul  -> "Mul"
    | Sub  -> "Sub"
    | Div  -> "Div"
    | Eval -> "Eval"
    | Iszero p -> "Iszero " ^ show p
end

type program_item =
  | Sc of string * int * list gm_code
  | Fd of fdecl

let rec lambda_lift = function
  | Ref v -> pure (Ref v)
  | Lit v -> pure (Lit v)
  | App (f, x) -> (| app (lambda_lift f) (lambda_lift x) |)
  | Lam (v, x) ->
    let! body = lambda_lift x
    let! (i, defs, known_sc) = get

    let vars =
      x |> free_vars
        |> S.delete v
        |> flip S.difference known_sc
        |> S.members

    let def = ("Lam" ^ show i, vars ++ [v], body)
    let app = foldl (fun f -> app f # Ref) (Ref ("Lam" ^ show i)) vars

    put (i + 1, Decl def :: defs, known_sc)
      |> map (const app)
  | Case (sc, alts) ->
      alts
        |> map (fun (_, x) -> x)
        |> foldl app sc
        |> lambda_lift

let rec eta_contract = function
  | Decl (n, a, e) as dec ->
    match a, e with
    | [], _ -> dec
    | xs, App (f, Ref v) ->
      if v == last xs && not (S.member v (free_vars f)) then
        eta_contract (Decl (n, init a, f))
      else
        dec
    | _, _ -> dec
  | Data c -> Data c
  | Foreign i -> Foreign i

let rec lambda_lift_sc = function
  | Decl (n, a, e) ->
    match e with
    | Lam (v, e) -> lambda_lift_sc (Decl (n, a ++ [v], e))
    | _ ->
      let! e = lambda_lift e
      let! _ = modify (fun (a, b, s) -> (a, b, S.insert n s))
      pure (Decl (n, a, e))
  | Data c -> Data c |> pure
  | Foreign i -> Foreign i |> pure

type dlist 'a <- list 'a -> list 'a

let cg_prim (Fimport { var, fent }) =
  let prim_math_op x =
    [ Push (Arg 0), Eval, Push (Arg 2), Eval, x, Update 2, Pop 2, Unwind ]
  let prim_equality =
    [ Push (Arg 0), Eval (* x, arg0, arg1, arg2, arg3 *)
    , Push (Arg 2), Eval (* y, x, arg0, arg1, arg2, arg3 *)
    , Sub                (* y - x, arg0, arg1, arg2, arg3 *)
    , Iszero ([ Push (Arg 3) ], [ Push (Arg 4) ])
    , Push (Int 0), Mkap, Update 4, Pop 4, Unwind ]
  match fent with
  | "add" -> Sc (var, 2, prim_math_op Add)
  | "sub" -> Sc (var, 2, prim_math_op Sub)
  | "mul" -> Sc (var, 2, prim_math_op Mul)
  | "div" -> Sc (var, 2, prim_math_op Div)
  | "equ" -> Sc (var, 4, prim_equality)
  | e -> error @@ "No such primitive " ^ e

let rec compile (env : M.t string int) = function
  | Ref v ->
    match M.lookup v env with
    | Some i -> (Push (Arg i) ::)
    | None -> (Push (Combinator v) ::)

  | App (f, x) ->
    let f = compile env f
    let x = compile (map (1 +) env) x
    f # x # (Mkap ::)

  | Lam _ ->
      error "Can not compile lambda expression, did you forget to lift?"
  | Case _ ->
      error "Can not compile case expression, did you forget to lift?"
  | Lit i -> (Push (Int i) ::)

let supercomb (_, args, exp) =
  let env = M.from_list (zip args [0..length args])
  let k = compile (M.from_list (zip args [0..length args])) exp
  k [Update (length env), Pop (length env), Unwind]

let known_scs = S.from_list [ "getchar", "putchar" ]

let program decs =
  let (decs, (_, lams, _)) =
    run_state (traverse (lambda_lift_sc # eta_contract) decs) (0, [], known_scs)
  let define nm =
    let! x = get
    if nm `S.member` x then
      error @@ "Redefinition of value " ^ nm
    else
      modify (S.insert nm)

  let go =
    flip traverse (lams ++ decs) @@ function
      | Decl ((nm, args, _) as sc) ->
        let! _ = define nm
        let code = supercomb sc
        Sc (nm, length args, code) |> pure
      | Data _ -> error "data declaration in compiler"
      | Foreign (Fimport { cc = Prim, var } as fi) ->
        let! _ = define var
        pure (cg_prim fi)
      | Foreign f -> pure (Fd f)
  let (out, _) = run_state go S.empty
  out
