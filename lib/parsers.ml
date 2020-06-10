open import "prelude.ml"
open import "./monads.ml"

private type consumed = C | E

private type error = Unexpected of string * list string

instance show error begin
  let show = function
    | Unexpected (s, []) -> s
    | Unexpected (s, ms) ->
      "Unexpected " ^ s ^ "\n"
        ^ "Expecting one of " ^ foldl (^) "" ms
end

private type pos <- { line : int, col : int }

private type result 'a =
  | Ok  of consumed * 'a    * string * pos
  | Err of consumed * error * string * pos

let join_consumed x y =
  match x with
  | C -> C
  | E -> y

type parser_t 'm 'a = private P of pos -> string -> 'm (result 'a)
type parser <- parser_t identity

instance functor 'm => functor (parser_t 'm) begin
  let f <$> P x = P @@ fun pos i ->
    flip map (x pos i) @@ fun p ->
    match p with
    | Ok (c, x, i) -> Ok (c, f x, i)
    | Err e -> Err e
end

instance monad 'm => applicative (parser_t 'm) begin
  let pure x = P (fun p s -> pure (Ok (E, x, s, p)))
  let P f <*> P x = P @@ fun p s ->
    let! f = f p s
    match f with
    | Ok (c, f, s, p) ->
      let! x = x p s
      match x with
      | Ok (c', x, s, p) -> pure @@ Ok (join_consumed c c', f x, s, p)
      | Err (c', p) -> pure @@ Err (join_consumed c c', p)
    | Err e -> pure @@ Err e
end

let x *> y = (fun _ x -> x) <$> x <*> y
let x <* y = (| const x y |)
let x <$ a = map (const x) a

instance monad 'm => monad (parser_t 'm) begin
  let P x >>= f = P @@ fun p s ->
    let! x = x p s
    match x with
    | Ok (c, x, s, p) ->
      let P kont = f x
      let! x = kont p s
      match x with
      | Ok (c', x, s) -> pure @@ Ok (join_consumed c c', x, s)
      | Err (c', p) -> pure @@ Err (join_consumed c c', p)
    | Err e -> pure @@ Err e
end

let private fail e = P (fun p s -> pure (Err (E, e, s, p)))

let empty : forall 'm 'a. monad 'm => parser_t 'm 'a =
  fail (Unexpected ("empty parse", []))

let unexpected e =
  fail (Unexpected (e, []))

let alt_err (Unexpected (u, xs)) (Unexpected (_, ys)) =
  Unexpected (u, xs ++ ys)

let P x <|> P y = P @@ fun p s ->
  let! x = x p s
  match x with
  | Ok x -> pure (Ok x)
  | Err (c, m, s, p) ->
    let! y = y p s
    match y with
    | Ok (c', x, s) -> pure (Ok (join_consumed c c', x, s))
    | Err (c', m', s) -> pure (Err (join_consumed c c', alt_err m m', s))

let P x <+> y = P @@ fun p s ->
  let! x = x p s
  match x with
  | Ok x -> pure (Ok x)
  | Err (c, m, s, p) ->
    let P y = force y
    let! y = y p s
    match y with
    | Ok (c', x, s) -> pure (Ok (join_consumed c c', x, s))
    | Err (c', m', s) -> pure (Err (join_consumed c c', alt_err m m', s))

private module S = import "lua/string.ml"

let char : forall 'm. applicative 'm => parser_t 'm string =
  P @@ fun p s ->
    let x = S.substring s 1 1
    if x <> "" then
      let r = S.substring s 2 (S.length s)
      if x == "\n" then
        pure @@ Ok (C, x, r, { line = p.line + 1, col = 0 })
      else
        pure @@ Ok (C, x, r, { line = p.line, col = p.col + 1 })
    else
      pure @@ Err (E, Unexpected ("end-of-file", ["character"]), s, p)

let eof : forall 'm. applicative 'm => parser_t 'm () =
  P @@ fun p s ->
    if s == "" then
      pure @@ Ok (E, (), s, p)
    else
      pure @@
        Err (E, Unexpected (S.substring s 1 1, ["end-of-file"]), s, p)

let satisfy pred =
  P @@ fun p s ->
    let x = S.substring s 1 1
    if x <> "" && pred x then
      let r = S.substring s 2 (S.length s)
      if x == "\n" then
        pure @@ Ok (C, x, r, { line = p.line + 1, col = 0 })
      else
        pure @@ Ok (C, x, r, { line = p.line, col = p.col + 1 })
    else
      let m =
        if x == "" then
          "end of file"
        else
          x
      pure @@ Err (E, Unexpected (m, ["character"]), s, p)

let P k <?> m = P @@ fun p s ->
  let! x = k p s
  match x with
  | Ok e -> pure (Ok e)
  | Err (c, Unexpected (u, _), s) -> pure (Err (c, Unexpected (u, [m]), s))

let many_fold k z (P x) =
  let rec go consumed kont pos s =
    let! x = x pos s
    match x with
    | Err ((c, _, s, pos) as p) ->
      match c with
      | C -> pure (Err p)
      | E -> kont consumed z pos s
    | Ok (c, x, s, pos) ->
      match c with
      | E -> error @@ "many: got parser that accepts the empty string"
      | C -> go C (fun c -> kont c # k x) pos s
  P (go E (fun c z pos s -> pure (Ok (c, z, s, pos))))

let many p = many_fold (::) [] p
let some p =
  let! x = p
  (x ::) <$> many p

let sep_by_1 sep p =
  let! x = p
  let! xs = many (sep *> p)
  pure (x :: xs)

let sep_by sep p = sep_by_1 sep p <|> pure []
external private val is_infix_of : string -> string -> bool =
  "function(s, s2) return s2:find(s) ~= nil end"

external private val is_prefix_of : string -> string -> bool =
  "function(s, s2) return (s2:find(s)) == 1 end"

let one_of chs =
  let len = S.length chs
  let rec loop ch i =
    if i > len then
      fail @@ Unexpected (ch, ["one of \"" ^ chs ^ "\""])
    else if ch == S.substring chs i i then
      pure ch
    else
      loop ch (i + 1)
  let! ch = char
  loop ch 1

let symbol str =
  let len = S.length str
  let rec loop acc i =
    if i > len then
      pure acc
    else
      let! c = char <?> S.substring str i i
      if c == S.substring str i i then
        loop (acc ^ c) (i + 1)
      else
        fail @@ Unexpected (acc ^ c, [S.substring str 1 i])
  loop "" 1

let between o c p =
  let! _ = o
  let! x = p
  let! _ = c
  pure x

let try (P x) = P @@ fun pos s ->
  let! x = x pos s
  match x with
  | Ok c -> pure (Ok c)
  | Err (_, p, _) -> pure (Err (E, p, s, pos))

let optionally p = map Some (try p) <|> pure None


let rec sep_end_by_1 sep p =
  let! x = p
  ( let! _ = sep
    let! xs = sep_end_by sep p
    pure (x :: xs)
  ) <|> pure [x]
and sep_end_by sep p =
  sep_end_by_1 sep p <|> pure []

let chainr1 p op =
  let rec scan =
    lazy (
      let! x = p
      rest x
    )
  and rest x =
    ( let! f = op
      let! y = force scan
      pure (f x y)
    ) <|> pure x
  let _ = rest (* shut up, amc *)
  force scan

let parse (P x) s =
  let! x = x { line = 0, col = 0 } s
  match x with
  | Ok (_, x, r) -> pure @@ Right (x, r)
  | Err (_, m, _, p) -> pure @@ Left (m, p)

let run_parser p s =
  let Id x = parse p s
  x

let run_parser' (P x) s =
  let Id x = x { line = 0, col = 0 } s
  x

let lift m = P @@ fun pos s ->
  let! x = m
  pure @@ Ok (E, x, s, pos)

let morph (k : forall 'a. 'm 'a -> 'n 'a) (P x) = P @@ fun p s -> k (x p s)
let void x = map (const ()) x
