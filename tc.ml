module M = import "data/map.ml"
module G = import "./lib/graph.ml"
open import "./lang.ml"
open import "amulet/exception.ml"
open import "prelude.ml"

type tc_tyvar 'a = Tv of {
  name : string, level : int, var : ref (option 'a)
}

instance eq (tc_tyvar 'a) begin
  let Tv x == Tv y = x.name == y.name
end

instance ord (tc_tyvar 'a) begin
  let Tv x `compare` Tv y = x.name `compare` y.name
end

type tc_kappa =
  | K_arr of tc_kappa * tc_kappa
  | K_star
  | K_var of tc_tyvar tc_kappa

type tc_rho =
  | T_uvar of tc_tyvar tc_rho
  | T_var of string
  | T_con of string
  | T_app of tc_rho * tc_rho
  | T_arr of tc_rho * tc_rho

instance show tc_rho begin
  let show =
    let rec show_arg = function
      | T_app _ as x -> "(" ^ go x ^ ")"
      | x -> show_domain x
    and show_domain = function
      | T_arr _ as x -> "(" ^ go x ^ ")"
      | x -> go x
    and go = function
      | T_uvar (Tv n) ->
          match !n.var with
          | Some t -> go t
          | None -> n.name
      | T_var v -> v
      | T_con v -> v
      | T_app (f, x) -> go f ^ " " ^ show_arg x
      | T_arr (a, b) -> show_domain a ^ " -> " ^ go b
    go
end

instance show tc_kappa begin
  let show x =
    let rec go = function
      | K_star -> "*"
      | K_var (Tv v) -> "?" ^ v.name
      | K_arr (a, b) -> show_domain a ^ " -> " ^ go b
    and show_domain = function
      | K_arr _ as x -> "(" ^ show x ^ ")"
      | x -> go x
    go x
end

type tc_sigma =
  Forall of {
    vars  : list string, 
    body  : tc_rho
  }

let rec free_unif_vars = function
  | T_uvar v -> S.singleton v
  | T_var _ -> S.empty
  | T_con _ -> S.empty
  | T_app (f, x) -> S.union (free_unif_vars f) (free_unif_vars x)
  | T_arr (a, b) -> S.union (free_unif_vars a) (free_unif_vars b)

let new_name =
  let c = ref 0
  fun () ->
    c := !c + 1
    "alpha" ^ show !c

let new_tcvar level =
  let name = new_name ()
  Tv { name, level, var = ref None }

let rec zonk = function
  | T_uvar (Tv r) as rho ->
    match !r.var with
    | Some rho -> zonk rho
    | None -> rho
  | T_var v -> T_var v
  | T_con v -> T_con v
  | T_app (f, x) -> T_app (zonk f, zonk x)
  | T_arr (f, x) -> T_arr (zonk f, zonk x)

let empty (Tv r) =
  match !r.var with
  | None -> true
  | Some (T_uvar (Tv r')) -> r.name == r'.name
  | _ -> false

let generalise level rho =
  let rho = zonk rho
  let vars =
    free_unif_vars rho
      |> S.filter (fun (Tv r) -> r.level > level && empty (Tv r))
      |> S.members
  flip iter vars @@ fun (Tv r) ->
    r.var := Some (T_var r.name)
  Forall { vars = map (fun (Tv r) -> r.name) vars, body = zonk rho }

let rec unify a b =
  let solve r s =
    match !r.var with
    | Some t -> unify t s
    | None -> r.var := Some s
  match a, b with
  | T_uvar (Tv r), b -> solve r b
  | a, T_uvar (Tv r) -> solve r a
  | T_var a, T_var b when a == b -> ()
  | T_con a, T_con b when a == b -> ()
  | T_app (f, x), T_app (f', x') ->
      unify f f'
      unify x x'
  | T_arr (a, b), T_arr (a', b') ->
      unify a a'
      unify b b'
  | a, b -> error @@ "Types " ^ show a ^ " and " ^ show b ^ " are not equal"

let rec unify_kappa a b =
  let solve r s =
    match !r.var with
    | Some t -> unify_kappa t s
    | None -> r.var := Some s
  match a, b with
  | K_var (Tv r), b -> solve r b
  | a, K_var (Tv r) -> solve r a
  | K_star, K_star -> ()
  | K_arr (a, b), K_arr (a', b') ->
      unify_kappa a a'
      unify_kappa b b'
  | a, b -> error @@ "Kinds " ^ show a ^ " and " ^ show b ^ " are not equal"

type scheme 'a = Poly of tc_sigma | Mono of 'a

instance show 'a => show (scheme 'a) begin
  let show = function
    | Poly (Forall {vars,body}) ->
        foldl (fun s i -> s ^ " " ^ i) "forall" vars ^ ". " ^ show body
    | Mono x -> show x
end

let mono m = function
  | Mono x -> x
  | Poly _ -> error @@ "Unexpected polytype " ^ m

let get_scope map var =
  match M.lookup var map with
  | Some v -> v
  | None -> error @@ "Name not in scope: " ^ var

let is_function_kind level tau =
  match tau with
  | K_arr (a, b) -> (a, b)
  | _ ->
      let a = new_tcvar level |> K_var
      let b = new_tcvar level |> K_var
      unify_kappa tau (K_arr (a, b))
      (a, b)

let rec infer_kind scope = function
  | Tyvar v ->
      let kappa = get_scope scope v |> mono "(kinds aren't ever polymorphic)"
      (T_var v, kappa)
  | Tycon v ->
      let kappa = get_scope scope v |> mono "(kinds aren't ever polymorphic)"
      (T_con v, kappa)
  | Tyapp (f, x) ->
      let (f, k_f) = infer_kind scope f
      let (x, k_x) = infer_kind scope x
      let (domain, result) = is_function_kind 0 k_f
      unify_kappa domain k_x
      (T_app (f, x), result)
  | Tyarr (a, b) ->
      let a = check_is_type scope a
      let b = check_is_type scope b
      (T_arr (a, b), K_star)
  | Tytup [] -> (T_con "Unit#", K_star)
  | _ -> error "Tuple types not supported"
and check_is_type scope t =
  let (t, k) = infer_kind scope t
  unify_kappa k K_star
  t

let rec default_to_star = function
  | K_var (Tv r) ->
      match !r.var with
      | Some k -> default_to_star k
      | None -> K_star
  | K_star -> K_star
  | K_arr (a, b) -> K_arr (default_to_star a, default_to_star b)


type dt_info <-
  { name : string, d_args : list string, c_args : list tc_rho, c_ret : tc_rho }

let mk_con_info (d_name : string) (d_args : list string) : list (string * list tc_rho) -> list dt_info =
  let go (name, args) =
    { name, c_args = args, d_args, c_ret = foldl (fun f x -> T_app (f, T_var x)) (T_con d_name) d_args }
  map go

let infer_data_group_kind scope (group : list _) =
  let init_kind (group, names) (name, args, constr) =
    let args =
      args |> map (fun v -> (v, new_tcvar 0 |> K_var |> Mono))
    let kind = foldl (fun t (_, r) -> K_arr (t, mono "" r)) K_star args
    let scope = M.from_list args
    ((name, kind, constr, scope, args) :: group, M.insert name (Mono kind) names)

  let (group, scope') = foldl init_kind ([], M.empty) group

  let scope = M.union scope scope'

  let group : list (string * tc_kappa * list string * list (string * list tc_rho)) =
    flip map group @@ fun (name, kind, constrs, args, args') ->
      let scope = M.union scope args
      constrs
        |> map (fun (Constr (name, args)) -> (name, map (check_is_type scope) args))
        |> (name,kind,[x|with (x,_)<-args'],)

  flip map group @@ fun (name, kind, args, constrs) ->
    (name, default_to_star kind, constrs, mk_con_info name args constrs)

let rec subst_vars f = function
  | T_var v as t ->
      match f v with
      | None -> t
      | Some t -> t
  | T_uvar (Tv v) as t ->
      match !v.var with
      | Some t -> subst_vars f t
      | None -> t
  | T_con v -> T_con v
  | T_app (a, b) -> T_app (subst_vars f a, subst_vars f b)
  | T_arr (a, b) -> T_arr (subst_vars f a, subst_vars f b)

let instantiate level (Forall { vars, body }) =
  let vars =
    vars
      |> map (fun v -> (v, new_tcvar level |> T_uvar))
      |> M.from_list
  subst_vars (flip M.lookup vars) body

let lookup_ty level scope v =
  get_scope scope v |> function
    | Mono t -> t
    | Poly s -> instantiate level s

let is_function_type level tau =
  match tau with
  | T_arr (a, b) -> (a, b)
  | _ ->
      let a = new_tcvar level |> T_uvar
      let b = new_tcvar level |> T_uvar
      unify tau (T_arr (a, b))
      (a, b)

(* TODO: Rank-N types *)
let is_subtype = unify

let rec infer dt_info level scope = function
  | Ref v -> lookup_ty level scope v |> (Ref v,)
  | App (f, x) ->
      let (f, arg, res) =
        infer dt_info level scope f
          |> second (is_function_type level)
      let x = check dt_info level scope arg x
      (App (f, x), res)
  | Lit i -> (Lit i, T_con "Int")
  | Let (bindings, body) ->
      let (bindings, scope') =
        infer_binding_group dt_info level scope bindings
      let (body, body_t) = infer dt_info level (scope `M.union` map force scope') body
      (Let (bindings, body), body_t)
  | x ->
      let t = new_tcvar level |> T_uvar
      let x = check dt_info level scope t x
      (x, t)

and check dt_info level scope wanted = function
  | Lam (arg, body) ->
      let (arg_t, body_t) = is_function_type level wanted
      let body =
        (* TODO: Rank-N types *)
        check dt_info level (M.insert arg (Mono arg_t) scope) body_t body
      Lam (arg, body)
  | Case (_, []) -> error "Empty case"
  | Case (scrutinee, Cons ((con, _, _), _) as patterns) ->
      let data =
        match M.lookup con dt_info with
        | Some data -> data
        | None -> error @@ "Constructor " ^ con ^ " doesn't belong to a type"

      let (scrutinee, scrut_t) = infer dt_info level scope scrutinee

      let go_arm {name, d_args, c_args, c_ret} (con, args, expr) =
        if name <> con then
          error @@ "Constructors out of order: expected this pattern to match " ^ name
        else ()

        if length c_args <> length args then
          error @@ "Constructor "
            ^ con ^ " has "
            ^ show (length c_args)
            ^ " but is being matched against with " ^ show (length args)
            ^ " variables"
        else ()

        let d_args =
          d_args
            |> map (fun v -> (v, new_tcvar level |> T_uvar))
            |> M.from_list
        let c_args = map (Mono # subst_vars (flip M.lookup d_args)) c_args
        let c_ret = subst_vars (flip M.lookup d_args) c_ret

        unify c_ret scrut_t

        let scope' = M.from_list (zip args c_args) `M.union` scope
        (con, args, check dt_info level scope' wanted expr)

      Case (scrutinee, zip_with go_arm data patterns)
  | x ->
      let (x, t) = infer dt_info level scope x
      is_subtype t wanted
      x

and infer_binding_group dt_info level (scope : M.t string _) bindings : _ * M.t string _ =
  let inner = level + 1
  let initial_types =
    bindings
      |> map (fun (name, _) -> (name, new_tcvar inner |> T_uvar |> Mono))
      |> M.from_list

  let initial_types = initial_types |> M.union scope

  let go_binding (bindings : list _, scope' : M.t _ _) (name : string, body : expr) =
    let (body, body_ty) =
      (fun () -> infer dt_info inner initial_types body)
        `catch` fun (e : some exception) ->
          error (describe_exception e ^ "\nwhen type checking " ^ name)
    M.lookup name scope
      |> function
        | Some (Mono t) -> unify t body_ty
        | _ -> ()
    (
      (name, body) :: bindings,
      M.insert name (lazy (generalise level body_ty |> Poly)) scope'
    )
  foldl go_binding ([], M.empty) bindings

let dependency_graph defs =
  let rec free_vars_of_cons t m (Constr (name, args)) =
    let cons =
      foldl (fun s t -> S.union s (free_cons t)) (S.singleton t)
        args
    M.insert name cons m
  let define n x m =
    M.alter (function
      | Some _ -> error @@ "Redefinition of value " ^ n
      | None -> Some x)
      n m
  let go (graph, defs) = function
    | Foreign (Fimport { var }) as x ->
        (M.insert var S.empty graph, define var x defs)
    | Decl (name, args, expr) as x ->
        let fvs =
          free_vars expr
            |> flip S.difference (S.from_list args)
            |> S.delete name
        (M.insert name fvs graph, define name x defs)
    | Data (name, _, cons) as x ->
        M.union graph (foldl (free_vars_of_cons name) M.empty cons)
          |> M.insert name S.empty
          |> (, define name x defs)
  let (graph, defs) = foldl go (M.empty, M.empty) defs
  (G.groups_of_sccs graph, defs)

let mk_lam args body = foldr (curry Lam) body args
let rec unlambda = function
  | Lam (v, x) ->
      let (args, x) = unlambda x
      (v :: args, x)
  | e -> ([], e)

let rec replicate n x =
  if n <= 0 then
    []
  else
    x :: replicate (n - 1) x

let rec add_missing_vars scope = function
  | Tyvar v ->
      match M.lookup v scope with
      | Some _ -> scope
      | None ->
        let k = new_tcvar 0 |> K_var
        M.insert v (Mono k) scope
  | Tycon _ -> scope
  | Tyapp (a, b) -> add_missing_vars (add_missing_vars scope b) a
  | Tyarr (a, b) -> add_missing_vars (add_missing_vars scope b) a
  | Tytup xs -> foldl add_missing_vars scope xs

let tc_program (prog : list decl) =
  let (plan, defs) = dependency_graph prog
  let tc_one (dt_info, val_scope, ty_scope, out) group =
    print (length out, length (S.members group))
    let defs = [ x | with name <- S.members group, with Some x <- [M.lookup name defs] ]
    match defs with
    | [] -> (dt_info, val_scope, ty_scope, out)
    | [Foreign (Fimport {var, ftype}) as def] ->
        let ty_scope' = add_missing_vars M.empty ftype
        let t = check_is_type (M.union ty_scope' ty_scope) ftype
        print var
        (dt_info, M.insert var (Forall { vars = M.keys ty_scope', body = t } |> Poly) val_scope, ty_scope, def :: out)
    | Cons (Foreign (Fimport {var}), _) ->
        error @@ "Foreign definition " ^ var ^ " is part of a group.  How?"
    | Cons (Decl (name, args, body), ds) ->
        let bindings =
          (name, mk_lam args body)
            :: [ (name, mk_lam args body) | with Decl (name, args, body) <- ds ]
        let (bindings, scope') = infer_binding_group dt_info -1 val_scope bindings
        let decs =
          [ Decl (name, unlambda expr) | with (name, expr) <- bindings ]
        print name
        (dt_info, M.union (map force scope') val_scope, ty_scope, foldr (::) decs out)
    | Cons (Data d, ds) ->
        let datas = d :: [ d | with Data d <- ds ]
        let r = infer_data_group_kind ty_scope datas
        let fix_constr (name, rhos : list tc_rho) =
          print name
          Constr (name, replicate (length rhos) (Tycon "#"))
        let rec go dt ty (vl : M.t string (scheme tc_rho)) ds = function
          | [] -> (dt, vl, ty, ds)
          | Cons ((name, kind, constrs, info : list dt_info), rest) ->
              go
                (foldl (fun i {name} -> M.insert name info i) dt info)
                (M.insert name (Mono kind) ty)
                (foldl
                  (fun s {name,d_args,c_args,c_ret} ->
                    M.insert name (Forall { vars = d_args, body = foldr (curry T_arr) c_ret c_args} |> Poly) s)
                  vl info)
                (Data (name, [], fix_constr <$> constrs) :: ds)
                rest
        go dt_info ty_scope val_scope out r
  let (_, _, _, p) = foldl tc_one (M.empty, M.empty, M.empty, []) plan
  p
