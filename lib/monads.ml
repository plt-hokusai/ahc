open import "prelude.ml"

type identity 'a = Id of 'a

instance functor identity begin
  let f <$> Id x = Id (f x)
end

instance applicative identity begin
  let pure = Id
  let Id f <*> Id x = Id (f x)
end

instance monad identity begin
  let Id x >>= f = f x
end

type state 's 'a = State of 's -> 'a * 's

let run_state (State k) = k

instance functor (state 's) begin
  let f <$> State x = State (first f # x)
end

instance applicative (state 's) begin
  let pure x = State (x,)
  let State f <*> State x = State @@ fun s ->
    let (f, s) = f s
    let (x, s) = x s
    (f x, s)
end

instance monad (state 's) begin
  let State x >>= f = State @@ fun s ->
    let (x, s) = x s
    run_state (f x) s
end

let get = State (fun s -> (s, s))
let put x = State (fun _ -> ((), x))
let modify f = State (fun s -> ((), f s))
