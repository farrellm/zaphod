{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Parser
  ( Parser,
    token,
    tokens,
  )
where

import qualified Control.Monad.Combinators.NonEmpty as NE (some)
import Text.Megaparsec hiding (token, tokens)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Zaphod.Types
import Prelude hiding (many, some)

type Parser = Parsec Void Text

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment ";;") (L.skipBlockComment "(*" "*)")

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

withSourcePos :: Parser (Raw' (Raw Loc)) -> Parser (Raw Loc)
withSourcePos p = do
  a <- getSourcePos
  t <- p
  b <- getSourcePos
  pure $ t :# Just (Loc a b)

unit :: Parser (Raw Loc)
unit = withSourcePos $ parens "" $> RUnit

pair :: Parser (Raw Loc)
pair = withSourcePos $ parens (RPair <$> token <* dot <*> token)

symbol_ :: Parser (Raw Loc)
symbol_ = withSourcePos $ RSymbol . Symbol <$> identifier

mkPair :: Raw Loc -> Raw Loc -> Raw Loc
mkPair l r = RPair l r :# (location l <> location r)

list :: Parser (Raw Loc)
list = do
  ts <- parens $ NE.some token
  pure (foldr mkPair (RUnit :# Nothing) ts)

tuple :: Parser (Raw Loc)
tuple = do
  ts <- brackets $ many token
  pure (foldr mkPair (RUnit :# Nothing) ("tuple" : ts))

mkQuote :: Char -> Symbol -> Parser (Raw Loc)
mkQuote c s = do
  t <- char c *> token
  pure $ mkPair (RSymbol s :# Nothing) (mkPair t (RUnit :# Nothing))

quote :: Parser (Raw Loc)
quote = mkQuote '\'' "quote"

backquote :: Parser (Raw Loc)
backquote = mkQuote '`' "backquote"

unquote :: Parser (Raw Loc)
unquote = mkQuote ',' "unquote"

token :: Parser (Raw Loc)
token =
  try unit
    <|> try quote
    <|> try backquote
    <|> try unquote
    <|> try symbol_
    <|> try pair
    <|> try tuple
    <|> try list

tokens :: Parser [Raw Loc]
tokens = (spaceConsumer <|> mempty) *> many token <* eof
