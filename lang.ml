open import "prelude.ml"
module S = import "data/set.ml"
module M = import "data/map.ml"

type expr =
  | Ref  of string
  | App  of expr * expr
  | Lam  of string * expr
  | Case of expr * list (string * expr)
  | Lit  of int

let app = curry App
let lam = curry Lam

let rec free_vars = function
  | Ref v -> S.singleton v
  | App (f, x) -> S.union (free_vars f) (free_vars x)
  | Lam (v, x) -> v `S.delete` free_vars x
  | Case (e, bs) ->
      bs
        |> map (fun (_, e) -> free_vars e)
        |> foldl S.union S.empty
        |> S.union (free_vars e)
  | Lit _ -> S.empty

let rec subst m = function
  | Ref v ->
    match M.lookup v m with
    | Some s -> s
    | None -> Ref v
  | App (f, x) -> App (subst m f, subst m x)
  | Lam (v, x) -> Lam (v, subst (M.delete v m) x)
  | Case (e, xs) -> Case (subst m e, map (second (subst m)) xs)
  | Lit x -> Lit x

type hstype =
  | Tycon of string
  | Tyvar of string
  | Tyapp of hstype * hstype
  | Tyarr of hstype * hstype
  | Tytup of list hstype

let rec arity = function
  | Tyarr (_, i) -> 1 + arity i
  | _ -> 0

type constr = Constr of string * list hstype

type call_conv = Lua | Prim

type fdecl =
  Fimport of {
    cc : call_conv,
    fent : string,
    ftype : hstype,
    var : string
  }

type decl =
  | Decl of string * list string * expr
  | Data of string * list string * list constr
  | Foreign of fdecl

type prog <- list decl

let rec xs !! i =
  match xs, i with
  | Cons (x, _), 0 -> x
  | Cons (_, xs), i when i > 0 -> xs !! (i - 1)
  | _, _ -> error "empty list and/or negative index"

let ds_data (_, _, cs) =
  let ncons = length cs
  let alts = map (("c" ^) # show) [1..ncons]
  let ds_con i (Constr (n, args)) =
    let arity = length args
    let alt = alts !! i
    let args = map (("x" ^) # show) [1..arity]
    Decl (n, args, foldr lam (foldl app (Ref alt) (map Ref args)) alts)
  let rec go i = function
    | [] -> []
    | Cons (x, xs) -> ds_con i x :: go (i + 1) xs
  go 0 cs

let ds_prog prog =
  let! c = prog
  match c with
  | Data c -> ds_data c
  | Decl (n, args, e) -> [Decl (n, args, e)]
  | Foreign d -> [Foreign d]
