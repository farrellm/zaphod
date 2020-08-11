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

-- brackets :: Parser a -> Parser a
-- brackets = between (symbol "[") (symbol "]")

-- semicolon :: Parser Text
-- semicolon = symbol ";"

-- comma :: Parser Text
-- comma = symbol ","

colon :: Parser Text
colon = symbol ":"

dot :: Parser Text
dot = symbol "."

-- backslash :: Parser Text
-- backslash = symbol "\\"

arrow :: Parser Text
arrow = symbol "->"

startingChar :: Parser Char
startingChar = lowerChar <|> char '_'

followingChar :: Parser Char
followingChar = alphaNumChar <|> char '_' <|> char '\''

--

identifier :: Parser Text
identifier = toText <$> lexeme ((:) <$> startingChar <*> many followingChar)

unit :: a -> Parser a
unit u = parens "" $> u

-- ZType

zUnit :: Parser ZType
zUnit = unit ZUnit

zFunction :: Parser ZType
zFunction = parens $ do
  x <- ztype
  ZFunction x <$> go
  where
    go = do
      y <- arrow *> ztype
      try (ZFunction y <$> go) <|> pure y

zVariable :: Parser ZType
zVariable = ZUniversal . Universal <$> identifier

ztype :: Parser ZType
ztype = try zUnit <|> try zFunction <|> zVariable

-- Untyped

tUnit :: Parser Untyped
tUnit = unit EUnit

tPair :: Parser Untyped
tPair = pair token (\a b -> EPair a b ())
  where
    pair p c = parens (c <$> p <* dot <*> p)

tSymbol :: Parser Untyped
tSymbol = ESymbol <$> identifier <*> pure ()

tList :: Parser Untyped
-- tList = TList <$> parens (NE.some token)
tList = parens $ do
  ts <- NE.some token
  pure (foldl' (\r l -> EPair l r ()) EUnit $ NE.reverse ts)

tTyping :: Parser Untyped
tTyping = parens (EAnnotation <$> token <* colon <*> ztype)

token :: Parser Untyped
token = try tUnit <|> try tSymbol <|> try tTyping <|> try tPair <|> tList

tokens :: Parser [Untyped]
tokens = many token <* eof
