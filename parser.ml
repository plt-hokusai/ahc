include import "./lang.ml"
include import "./lexer.ml"
open import "prelude.ml"

let parse = lex

let laid_out_block p = between obrace cbrace (sep_end_by_1 semi p)

let rec atom : forall 'm. monad 'm => parser_t 'm expr =
  map Ref (try varid)
    <+> map Ref (try conid)
    <+> between (try oparen) cparen expr
and fexp : forall 'm. monad 'm => parser_t 'm expr =
  let! a = atom
  let! ats = many atom
  pure (foldl (curry App) a ats)
and expr : forall 'm. monad 'm => parser_t 'm expr =
  let lam =
    let! _  = back
    let! vs = many (try varid)
    let! _  = arrow
    let! b  = expr
    pure (foldr ((Lam #) # curry id) b vs)
  let case =
    let! _ = keyword "case"
    let! e = fexp
    let! _ = keyword "of"
    let! arms =
      laid_out_block (
        let! c = conid
        let! vs = many (try varid)
        let! _ = arrow
        let! e = expr
        pure (c, foldr ((Lam #) # curry id) e vs)
      )
    pure (Case (e, arms))
  try lam <|> try case <+> fexp

let rec ty_atom : forall 'm. monad 'm => parser_t 'm hstype =
  map Tyvar (try varid)
    <|> map Tycon (try conid)
    <+> between (try oparen) cparen ty_exp
and ty_exp : forall 'm. monad 'm => parser_t 'm hstype =
  let! a = ty_atom
  let! ats = many ty_atom
  pure (foldl (curry Tyapp) a ats)

let datadec : forall 'm. monad 'm => parser_t 'm decl =
  let! _ = keyword "data"
  let datacon =
    let! nm = conid
    let! args = many ty_atom
    pure (Constr (nm, args))
  let! nm = conid
  let! args = many (try varid)
  let! _ = equals
  let! c = sep_by_1 pipe (try datacon)
  pure (Data (nm, args, c))

let dec : forall 'm. monad 'm => parser_t 'm decl =
  let func =
    let! nm = varid
    let! args = many (try varid)
    let! _ = equals
    map (fun e -> Decl (nm, args, e)) expr
  try datadec <|> func

let prog : forall 'm. monad 'm => parser_t 'm prog =
  sep_end_by_1 semi dec <* eof
