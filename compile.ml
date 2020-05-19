module M = import "data/map.ml"
module S = import "data/set.ml"

open import "prelude.ml"
open import "./lang.ml"
open import "./lib/monads.ml"

type addr =
  | Combinator of string
  | Local of int
  | Arg of int
  | Int of int

type gm_code =
  | Push of addr
  | Update of int
  | Pop of int
  | Slide of int
  | Alloc of int
  | Unwind
  | Mkap
  | Add | Sub | Mul | Div | Eval
  | Iszero of list gm_code * list gm_code
  | Pack of int * int
  | Casejump of list (int * list gm_code)

instance show gm_code begin
  let show = function
    | Mkap -> "Mkap"
    | Unwind -> "Unwind"
    | Push (Combinator k) -> "Push " ^ k
    | Push (Arg i) -> "Pusharg " ^ show i
    | Push (Local i) -> "Pushlocal " ^ show i
    | Push (Int i) -> "Pushint " ^ show i
    | Update n -> "Update " ^ show n
    | Pop n   -> "Pop " ^ show n
    | Slide n -> "Slide " ^ show n
    | Alloc n -> "Alloc " ^ show n
    | Add  -> "Add"
    | Mul  -> "Mul"
    | Sub  -> "Sub"
    | Div  -> "Div"
    | Eval -> "Eval"
    | Pack (arity, tag) -> "Pack{" ^ show arity ^ "," ^ show tag ^ "}"
    | Casejump xs -> "Casejump " ^ show xs
    | Iszero xs -> "Iszero " ^ show xs
end

type program_item =
  | Sc of string * int * list gm_code
  | Fd of fdecl

instance show program_item begin
  let show = function
    | Sc p -> show p
    | Fd _ -> "<foreign item>"
end

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
    let! sc = lambda_lift sc
    let! alts = traverse (fun (c, args, e) -> (c,args,) <$> lambda_lift e) alts
    let case = Case (sc, alts)
    let! (i, defs, known_sc) = get
    let vars =
      case
        |> free_vars
        |> flip S.difference known_sc
        |> S.members
    let def = ("Lam" ^ show i, vars, case)
    let app = foldl (fun f -> app f # Ref) (Ref ("Lam" ^ show i)) vars
    put (i + 1, Decl def :: defs, known_sc)
      |> map (const app)
  | Let (vs, e) ->
    let! vs = flip traverse vs @@ fun (v, e) ->
      (v,) <$> lambda_lift e
    let! e = lambda_lift e
    pure (Let (vs, e))

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
  | Foreign (Fimport { var } as i) ->
      let! _ = modify (second (second (S.insert var)))
      Foreign i |> pure

type dlist 'a <- list 'a -> list 'a

let cg_prim (Fimport { var, fent }) =
  let prim_math_op x =
    [ Push (Arg 0), Eval, Push (Arg 2), Eval, x, Update 2, Pop 2, Unwind ]
  let prim_equality =
    [ Push (Arg 0), Eval (* x, arg0, arg1, arg2, arg3 *)
    , Push (Arg 2), Eval (* y, x, arg0, arg1, arg2, arg3 *)
    , Sub                (* y - x, arg0, arg1, arg2, arg3 *)
    , Iszero ([ Push (Arg 3) ], [ Push (Arg 4) ])
    , Update 4, Pop 4, Unwind ]
  match fent with
  | "add" -> (Sc (var, 2, prim_math_op Add), Add)
  | "sub" -> (Sc (var, 2, prim_math_op Sub), Sub)
  | "mul" -> (Sc (var, 2, prim_math_op Mul), Mul)
  | "div" -> (Sc (var, 2, prim_math_op Div), Div)
  | "equ" -> (Sc (var, 4, prim_equality), Unwind)
  | "seq" -> (Sc (var, 2, [ Push (Arg 0), Eval, Update 0, Push (Arg 2), Update 2, Pop 2, Unwind]), Eval)
  | e -> error @@ "No such primitive " ^ e

type slot = As of int | Ls of int

let offs n = function
  | As x -> As (x + n)
  | Ls x -> Ls (x + n)
let incr = offs 1

let rec compile (env : M.t string slot) = function
  | Ref v ->
    match M.lookup v env with
    | Some (As i) -> (Push (Arg i) ::)
    | Some (Ls i) -> (Push (Local i) ::)
    | None -> (Push (Combinator v) ::)

  | App (f, x) ->
    let f = compile env f
    let x = compile (map incr env) x
    f # x # (Mkap ::)

  | Lam _ ->
      error "Can not compile lambda expression, did you forget to lift?"
  | Case (sc, alts) ->
    let rec go_alts = function
      | [] -> []
      | Cons ((_, args, exp), rest) ->
        let c_arity = length args
        let env =
          args
            |> flip zip [Ls k | with k <- [c_arity - 1, c_arity - 2 .. 0]]
            |> M.from_list
            |> M.union (offs (c_arity + 1) <$> env)
        (c_arity, compile env exp [Slide c_arity]) :: go_alts rest
    compile env sc # (Eval ::) # (Casejump (go_alts alts) ::)
  | Lit i -> (Push (Int i) ::)
  | Let (vs, e) ->
    let n = length vs
    let env =
      vs
        |> map (fun (x, _) -> x)
        |> flip zip [Ls x | with x <- [n - 1, n - 2 .. 0]]
        |> M.from_list
        |> M.union (offs n <$> env)
    let defs = zip [1..n] vs
    let rec go : list (int * string * expr) -> dlist gm_code = function
      | [] -> id
      | Cons ((k, (_, exp)), rest) ->
          compile env exp # (Update (n - k) ::) # go rest
    (Alloc n ::) # go defs # compile env e # (Slide n ::)

let supercomb (_, args, exp) =
  let env = M.from_list (zip args [0..length args])
  let k = compile (M.from_list (zip args (As <$> [0..length args]))) exp
  k [Update (length env), Pop (length env), Unwind]

let compile_cons =
  let rec go i = function
    | [] -> []
    | Cons (Constr (n, args), rest) ->
      let arity = length args
      let rec pushargs i =
        if i < arity then
          Push (Arg (2 * i)) :: pushargs (i + 1)
        else
          []
      Sc (n, arity, pushargs 0 ++ [ Pack (arity, i), Update (2 * arity), Pop (2 * arity), Unwind ])
        :: go (i + 1) rest
  go 0

let program decs =
  let (decs, (_, lams, _)) =
    run_state (traverse (lambda_lift_sc # eta_contract) decs)
      (0, [], S.empty)
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
        [Sc (nm, length args, code)] |> pure
      | Data (_, _, cs) -> pure (compile_cons cs)
      | Foreign (Fimport { cc = Prim, var } as fi) ->
        let! _ = define var
        let (code, _) = cg_prim fi
        pure [code]
      | Foreign f -> pure [Fd f]
  let (out, _) = run_state go S.empty
  join out
