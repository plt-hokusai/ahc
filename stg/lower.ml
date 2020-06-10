open import "prelude.ml"
module Src = import "../lang.ml"
open Src

module Map = import "data/map.ml"
module Set = import "data/set.ml"
module Stg = import "./stg.ml"

let spine f =
  let rec spine = function
    | App (f, x) ->
      let (f, args) = spine f
      (f, x :: args)
    | e -> (e, [])
  let (f, args) = spine f
  (f, reverse args)

let rec napp f = function
  | [] -> f
  | Cons (x, xs) -> napp (App (f, x)) xs

let get_con_arities prog =
  let go_con m (Constr (name, tys)) = M.insert name (length tys) m
  let go m = function
    | Data (_, _, cons) -> foldl go_con m cons
    | _ -> m
  foldl go M.empty prog

let gensym =
  let counter = ref 0
  fun () ->
    counter := !counter + 1
    "_s" ^ show !counter

let rec add_n_args da exp =
  if da <= 0 then
    exp
  else
    let var = gensym ()
    Lam (var, App (add_n_args (da - 1) exp, Ref var))

let rec eta_expand_cons arities =
  let rec go = function
    | Case (exp, alts) -> Case (go exp, map (second (second go)) alts)
    | Lam (var, alts) -> Lam (var, go alts)
    | If (a, b, c) -> If (go a, go b, go c)
    | Let (decs, body) -> Let (map (second go) decs, go body)
    | exp ->
      match spine exp with
      | Ref func, args ->
        let arg_len = length args
        match Map.lookup func arities with
        | Some arity when arity > arg_len -> add_n_args (arity - arg_len) (napp (Ref func) args)
        | _ -> exp
      | _, _ -> error @@ "What?"
  go

let build_stg_app func = function
  | [] -> Stg.Atom func
  | args -> Stg.(App (func, args))

let mk_lambda_form name exp =
  let free_vars = Stg.stg_fv exp
  { name, free_vars, update = Stg.Updatable, args = [], body = exp }

let mk_function name args exp =
  let free_vars = foldl (flip Set.delete) (Stg.stg_fv exp) args
  { name, free_vars, update = Stg.Function, args, body = exp }

let rec unlambda = function
  | Lam (var, body) ->
    let (args, body) = unlambda body
    (var :: args, body)
  | e -> ([], e)

let rec lower_spine (func, args) kont =
  lower_atom func @@ fun func ->
    let rec go kont lowered = function
      | [] -> kont (build_stg_app func (reverse lowered))
      | Cons (Ref e, args) ->
        go kont (Stg.Var e :: lowered) args
      | Cons (Lit i, args) ->
        go kont (Stg.Int i :: lowered) args
      | Cons (arg, args) ->
        lower_atom arg @@ fun arg ->
          go kont (arg :: lowered) args
    go kont [] args
and lower exp kont =
  match spine exp with
  | exp, [] ->
    match exp with
    | App _ -> error @@ "Impossible lower App with empty spine"
    
    (* STG atoms *)
    | Ref e -> kont Stg.(Atom (Var e))
    | Lit e -> kont Stg.(Con (0, 1, [Int e]))

    (* Lambdas need to be bound as lambda-forms *)
    | Lam _ as lam ->
      let name = gensym ()
      let (args, body) = unlambda lam
      let body = lower_body body
      Stg.Let ([mk_function name args body], kont Stg.(Atom (Var name)))

    | If (cond, th, el) ->
      lower cond @@ fun cond ->
        lower th @@ fun th ->
          lower el @@ fun el ->
            Stg.( Case (cond, "binder" ^ gensym(), [(Con_pat (0, []), th), (Default, el)]) )
              |> kont

    | Let (bindings, body) ->
      lower_binds bindings @@ fun lambda_forms ->
        Stg.Let (lambda_forms, lower body kont)
    
    | Case (scrut, arms) ->
      lower scrut @@ fun scrut ->
        lower_arms arms @@ fun arms ->
          Stg.Case (scrut, "binder" ^ gensym(), arms) |> kont
  | e -> lower_spine e kont

and lower_atom exp kont =
  lower exp @@ function
    | Stg.Atom at -> kont at
    | e ->
      let name = gensym ()
      Stg.(Let ([mk_lambda_form name e], kont (Var name)))

and lower_binds bindings kont =
  let rec go acc = function
    | [] -> kont (reverse acc)
    | Cons ((name, bind), rest) ->
      go (lower_rhs name bind :: acc) rest
  go [] bindings

and lower_arms arms kont =
  let rec go i acc = function
    | [] -> kont (reverse acc)
    | Cons ((_, args, exp), rest) ->
      let body = lower_body exp
      go (i + 1) ((Stg.(Con_pat (i, args)), body) :: acc) rest
  go 0 [] arms

and lower_rhs name exp =
  match exp with
  | Lam _ as lam -> 
    let (args, body) = unlambda lam
    let body = lower_body body
    mk_function name args body
  | _ ->
    let body = lower_body exp
    mk_lambda_form name body

and lower_body exp = lower exp (fun x -> x)

let mk_stg_prim name prim =
  let binary_prim x =
    let open Stg
    let body =
      Case (Atom (Var "x"), "x",
        [( Default, Case (Atom (Var "y"), "y",
          [(Default, Prim (x, [Var "x", Var "y"]))]))])
    Fun { name, args = ["x", "y"], body, is_con = None }
  match prim with
  | "add" -> binary_prim Stg.Add
  | "sub" -> binary_prim Stg.Sub
  | "mul" -> binary_prim Stg.Mul
  | "div" -> binary_prim Stg.Div
  | "equ" -> binary_prim Stg.Equ
  | e -> error @@ "No such primitive " ^ e

let lower_dec = function
  | Decl (name, manifest_args, expr) ->
    let (args, body) = unlambda expr
    let args = manifest_args ++ args
    let body = lower_body body
    [ Stg.Fun { name, args, body, is_con = None } ]
  | Data (_, _, cons) ->
    let mk_stg_con (Constr (name, args), i) =
      let args = [ gensym () | with _ <- args ]
      Stg.Fun { name, args, body = build_stg_app (Stg.Var name) (Stg.Var <$> args), is_con = Some i }
    [ mk_stg_con c | with c <- zip cons [0 .. length cons - 1] ]
  | Foreign (Fimport { cc = Prim, fent = prim, var = name }) ->
    [ mk_stg_prim name prim ]
  | Foreign (Fimport { cc = Lua, fent, var, ftype }) ->
    [ Stg.Ffi_def { name = var, fent, arity = arity ftype }]