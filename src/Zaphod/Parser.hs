{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Parser
  ( Parser,
    token,
    tokens,
  )
where

import qualified Control.Monad.Combinators.NonEmpty as NE (some)
import qualified Data.List.NonEmpty as NE (reverse)
import Text.Megaparsec hiding (token, tokens)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Zaphod.Types
import Prelude hiding (many, some)

type Parser = Parsec Void Text

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "(*" "*)")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = L.symbol spaceConsumer

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- braces :: Parser a -> Parser a
-- braces = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

-- semicolon :: Parser Text
-- semicolon = symbol ";"

-- comma :: Parser Text
-- comma = symbol ","

-- colon :: Parser Text
-- colon = symbol ":"

dot :: Parser Text
dot = symbol "."

-- backslash :: Parser Text
-- backslash = symbol "\\"

-- arrow :: Parser Text
-- arrow = symbol "->"

startingChar :: Parser Char
startingChar = letterChar <|> symbolChar <|> oneOf (":!@#%&-_" :: [Char])

followingChar :: Parser Char
followingChar = startingChar <|> digitChar <|> char '\''

--

identifier :: Parser Text
identifier = toText <$> lexeme ((:) <$> startingChar <*> many followingChar)

-- Raw

unit :: Parser Raw
unit = parens "" $> RUnit

pair :: Parser Raw
pair = parens (RPair <$> token <* dot <*> token)

symbol_ :: Parser Raw
symbol_ = RSymbol . Symbol <$> identifier

list :: Parser Raw
list = parens $ do
  ts <- NE.some token
  pure (foldl' (\r l -> RPair l r) RUnit $ NE.reverse ts)

tuple :: Parser Raw
tuple = brackets $ do
  ts <- many token
  pure (foldl' (\r l -> RPair l r) RUnit $ reverse ("list" : ts))

quote :: Parser Raw
quote = char '\'' *> (q <$> token)
  where
    q x = (RPair "quote" (RPair x RUnit))

token :: Parser Raw
token =
  try unit
    <|> try symbol_
    <|> try pair
    <|> try tuple
    <|> try list
    <|> try quote

tokens :: Parser [Raw]
tokens = many token <* eof
