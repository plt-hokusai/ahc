open import "prelude.ml"
module S = import "data/set.ml"
module M = import "data/map.ml"

type expr =
  | Ref  of string
  | App  of expr * expr
  | Lam  of string * expr
  | Case of expr * list (string * list string * expr)
  | Lit  of int
  | Let  of list (string * expr) * expr

let app = curry App
let lam = curry Lam

let rec free_vars = function
  | Ref v -> S.singleton v
  | App (f, x) -> S.union (free_vars f) (free_vars x)
  | Lam (v, x) -> v `S.delete` free_vars x
  | Case (e, bs) ->
      bs
        |> map (fun (_, a, e) -> free_vars e `S.difference` S.from_list a)
        |> foldl S.union S.empty
        |> S.union (free_vars e)
  | Let (vs, b) ->
      let bound = S.from_list (map (fun (x, _) -> x) vs)
      vs
        |> map (fun (_, e) -> free_vars e)
        |> foldl S.union S.empty
        |> S.union (free_vars b)
        |> flip S.difference bound
  | Lit _ -> S.empty

type hstype =
  | Tycon of string
  | Tyvar of string
  | Tyapp of hstype * hstype
  | Tyarr of hstype * hstype
  | Tytup of list hstype

let rec free_cons = function
  | Tycon v -> S.singleton v
  | Tyvar _ -> S.empty
  | Tyapp (f, x) -> S.union (free_cons f) (free_cons x)
  | Tyarr (f, x) -> S.union (free_cons f) (free_cons x)
  | Tytup xs -> foldl (fun s x -> S.union s (free_cons x)) S.empty xs

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
