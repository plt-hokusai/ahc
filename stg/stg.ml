module Set = import "data/set.ml"
open import "prelude.ml"

type update_flag = Updatable | Function

type lambda_form 'a <- { name : string, free_vars : Set.t string, args : list string, update : update_flag, body : 'a }

type stg_atom =
  | Var of string
  | Int of int

type stg_pattern =
  | Con_pat of int * list string
  | Default

type stg_primitive =
  | Add
  | Sub
  | Mul 
  | Div
  | Equ

type stg_expr =
  | Let  of list (lambda_form stg_expr) * stg_expr
  | Case of stg_expr  * string * list (stg_pattern * stg_expr)
  | App  of stg_atom  * list stg_atom
  | Con  of int * int * list stg_atom
  | Prim of stg_primitive * list stg_atom
  | Atom of stg_atom

type stg_def =
  | Fun     of { name : string, args : list string, body : stg_expr, is_con : option int }
  | Ffi_def of { name : string, fent : string, arity : int }

let stg_fv =
  let rec go = function
    | Atom a -> go_atom a
    | Let (lfs, e) ->
      let fv = go e
      fv `Set.difference` Set.from_list (map (.name) lfs)
    | App (a, args) -> foldl Set.union Set.empty (map go_atom (a::args))
    | Con (_, _, i) -> foldl Set.union Set.empty (map go_atom i)
    | Case (ex, binder, pats) ->
      foldl go_pat (go ex) pats
        |> Set.delete binder
    | Prim (_, args) -> foldl Set.union Set.empty (map go_atom args)
  and go_atom = function
    | Int _ -> Set.empty
    | Var e -> Set.singleton e
  and go_pat set = function
    | Default, e -> Set.union set (go e)
    | Con_pat (_, args), e -> Set.union set (go e `Set.difference` Set.from_list args)
  go