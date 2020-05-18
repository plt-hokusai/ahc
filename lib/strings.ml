module S = import "lua/string.ml"
open import "prelude.ml"

let split_on ch str =
  let len = S.length str
  let rec go i acc acc' = 
    if i > len then
      reverse (acc :: acc')
    else
      let this = S.substring str i i
      if this == ch then
        go (i + 1) "" (acc :: acc')
      else
        go (i + 1) (acc ^ this) acc'
  go 1 "" []

