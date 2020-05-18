include import "./lib/parsers.ml"
open import "prelude.ml"

let lex = run_parser

let line_comment () =
  let! _ = symbol "--"
  let rec go =
    let! x = map (const "\n") eof <|> char
    if x == "\n" then
      pure ()
    else
      go
  go

let whitepiece : forall 'm. monad 'm => parser_t 'm () =
  (try (void @@ one_of " \n\v\t\r") <|> try (line_comment ()))
    <?> "white space"

let whitespace : forall 'm. monad 'm => parser_t 'm () =
  void (many whitepiece)

let lexeme p =
  let! _ = whitespace
  p

let oparen  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "(")
let cparen  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol ")")
let comma   : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol ",")
let semi    : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol ";")
let osquare : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "[")
let csquare : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "]")
let obrace  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "{")
let cbrace  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "}")
let back    : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "\\")
let arrow   : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "->")
let darrow  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "=>")
let equals  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "=")
let pipe    : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "|")
let dcolon  : forall 'm. monad 'm => parser_t 'm () = try @@ void @@ lexeme (symbol "::")

let small : forall 'm. monad 'm => parser_t 'm string =
  try (satisfy (fun c -> "a" <= c && c <= "z") <|> symbol "_") <?> "small letter"

let big : forall 'm. monad 'm => parser_t 'm string =
  try (satisfy (fun c -> "A" <= c && c <= "Z")) <?> "big letter"

let iskw = function
  | "case"
  | "class"
  | "data"
  | "default"
  | "deriving"
  | "do"
  | "else"
  | "if"
  | "import"
  | "in"
  | "infix"
  | "infixl"
  | "infixr"
  | "instance"
  | "let"
  | "module"
  | "newtype"
  | "of"
  | "foreign"
  | "then"
  | "type"
  | "where"
  | "_" -> true
  | _ -> false

let isreserved = function
  | "=" | "=>" | "->" | "|" -> true
  | _ -> false

let varid : forall 'm. monad 'm => parser_t 'm string =
  flip (<?>) "variable name" # lexeme @@
    let! c = small
    let! cs =
      many_fold (^) "" (small <|> big <|> try (symbol "'"))
        <|> pure ""
    let id = c ^ cs
    if iskw id then
      unexpected id
    else
      pure id

let conid : forall 'm. monad 'm => parser_t 'm string =
  flip (<?>) "constructor name" # lexeme @@
    let! c = big
    let! cs =
      many_fold (^) "" (small <|> big <|> try (symbol "'"))
        <|> pure ""
    pure (c ^ cs)

let tyvar = varid
let tycon = conid
let tycls = conid

let keyword c = lexeme (symbol c) <?> "``" ^ c ^ "''"

let operator : forall 'm. monad 'm => parser_t 'm string =
  flip (<?>) "operator" # lexeme @@
    let! c = one_of "!#$%&*+./<=>?@\\^|-~"
    let! cs = many_fold (^) "" (one_of ":!#$%&*+./<=>?@\\^|-~")
    let op = c ^ cs
    if isreserved op then
      unexpected op
    else
      pure op

let digit : forall 'm. monad 'm => parser_t 'm string =
  satisfy (fun c -> "0" <= c && c <= "9") <?> "digit"

let hexit : forall 'm. monad 'm => parser_t 'm string =
  digit
    <|> satisfy (fun c -> "a" <= c && c <= "f")
    <|> satisfy (fun c -> "A" <= c && c <= "F")

let integer : forall 'm. monad 'm => parser_t 'm int =
  let decimal =
    let! c = digit
    let! cs = many_fold (^) "" digit
    pure (c ^ cs)
  let hexadecimal =
    let! _ = symbol "0x"
    let! c = hexit
    let! cs = many_fold (^) "" hexit
    pure ("0x" ^ c ^ cs)
  let! c = (lexeme (try hexadecimal <|> decimal)) <?> "hex or decimal integer"
  match parse_int c with
  | None -> error "no parse"
  | Some x -> pure x

let string : forall 'm. monad 'm => parser_t 'm string =
  flip (<?>) "string literal" # lexeme @@
    let parse_escape = function
      | "n" -> pure "\n"
      | "t" -> pure "\t"
      | "\"" -> pure "\""
      | a -> unexpected ("escape sequence " ^ a)
    let str_ent =
      satisfy (fun p -> p <> "\"" && p <> "\\")
        <|> ( let! _ = try (symbol "\\")
              let! e = char
              parse_escape e)
    symbol "\"" *> many_fold (^) "" str_ent <* symbol "\""
