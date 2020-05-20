module M = import "data/map.ml"
module S = import "data/set.ml"

open import "prelude.ml"

type t 'a <- M.t 'a (S.t 'a)

let sccs (graph : t 'a) =
  let rec dfs (node : 'a) (path : M.t 'a int) (sccs : M.t 'a 'a) =
    let shallower old candidate =
      match M.lookup old path, M.lookup candidate path with
      | _, None -> old
      | None, _ -> candidate
      | Some a, Some b ->
          if b < a then candidate else old
    let children =
      match M.lookup node graph with
      | Some t -> t
      | None -> error "Node not in graph?"
    let go (folded, shallowest) child =
        match M.lookup child path with
        | Some _ ->
            (folded, shallower shallowest child)
        | _ ->
            let scc = dfs child (M.insert node (length path) path) folded
            let sfc =
              match M.lookup child scc with
              | Some x -> x
              | None -> error "no child in scc?"
            (scc, shallower shallowest sfc)
    let (new, shallowest) =
      S.members children |> foldl go (sccs, node)
    M.insert node shallowest new
  let go sccs next =
    match M.lookup next sccs with
    | Some _ -> sccs
    | _ -> dfs next M.empty sccs
  graph
    |> M.keys
    |> foldl go M.empty

let toposort (graph : t 'a) : list 'a =
  let nodes = M.keys graph
  let l = ref []
  let temp = ref S.empty
  let perm = ref S.empty
  let rec visit n =
    if n `S.member` !perm then
      ()
    else if n `S.member` !temp then
      error "not a dag"
    else
      let o_temp = !temp
      temp := S.insert n o_temp
      match M.lookup n graph with
      | None -> ()
      | Some xs -> iter visit (S.members xs)
      temp := o_temp
      perm := S.insert n !perm
      l := n :: !l
  iter visit nodes
  reverse !l

let dot_of_graph (graph : t 'a) =
  let mk node =
    S.foldr (fun edge r -> show node ^ " -> " ^ show edge ^ "\n" ^ r) "\n"
  "strict digraph {"
    ^ M.foldr_with_key (fun node edges r -> mk node edges ^ r) "" graph
    ^ "}"

let groups_of_sccs (graph : t 'a) =
  let sccs = sccs graph
  let edges_of n =
    match M.lookup n graph with
    | None -> error "not in graph"
    | Some v -> v
  let components =
    sccs
      |> M.assocs
      |> map (fun (k, s) -> M.singleton s (S.singleton k))
      |> foldl (M.union_by (fun _ -> S.union)) M.empty
  let atd nodes =
    S.foldr (fun n -> S.union (edges_of n)) S.empty nodes `S.difference` nodes
  let comp_deps =
     components
       |> M.assocs
       |> map (fun (node, edges) -> (node, atd edges))
       |> M.from_list
  let ordering = toposort comp_deps
  [ x | with k <- ordering, with Some x <- [M.lookup k components] ]
