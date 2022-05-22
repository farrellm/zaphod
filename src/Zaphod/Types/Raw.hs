{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Zaphod.Types.Raw where

import Prettyprinter (Pretty (pretty), align, brackets, parens, sep, (<+>))
import Zaphod.Types.Class (Location (..), Magma (..), MaybeList (..), Render (..))
import Zaphod.Types.Location (LocF (..), LocU (..))
import Zaphod.Types.Wrapper (Symbol (..))

data RawF k
  = RUnit
  | RSymbol Symbol
  | RTsSymbol Symbol Int
  | RPair k k
  deriving (Show, Eq, Functor)

type Raw = LocF RawF

type Raw' = LocU RawF

deriving instance Show (LocU RawF)

deriving instance Eq (LocU RawF)

deriving instance (Show l) => Show (LocF RawF l)

instance Eq (Raw l) where
  (a :# _) == (b :# _) = a == b

instance Render (Raw l) where
  render (RUnit :# _) = "()"
  render (RSymbol s :# _) = render s
  render (RTsSymbol s n :# _) = render s <> "@" <> show n
  render (RPair (RS "quote") r :# _) = "'" <> render r
  render (RPair (RS "quasiquote") r :# _) = "`" <> render r
  render (RPair (RS "unquote") r :# _) = "," <> render r
  render (RPair (RS "unquote-splicing") r :# _) = ",@" <> render r
  render p@(RPair l r :# _) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)

instance MaybeList (Raw l) where
  isList (RUnit :# _) = True
  isList (RPair _ r :# _) = isList r
  isList _ = False

  maybeList (RUnit :# _) = Just []
  maybeList (RPair l r :# _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance (Location l) => Magma (Raw l) where
  x@(_ :# lx) >< y@(_ :# ly) = RPair x y :# (lx <> ly)

viewSymbol :: Raw l -> Maybe Symbol
viewSymbol (RSymbol s :# _) = Just s
viewSymbol (RTsSymbol s _ :# _) = Just s
viewSymbol _ = Nothing

pattern RU :: Raw l
pattern RU <- RUnit :# _

pattern RS :: Symbol -> Raw l
pattern RS s <- (viewSymbol -> Just s)

pattern (:.) :: Raw l -> Raw l -> Raw l
pattern (:.) x y <- RPair x y :# _

infixr 5 :.

{-# COMPLETE RU, RS, (:.) #-}

rawTuple :: Location l => NonEmpty (Raw l) -> Raw l
rawTuple (x@(_ :# l) :| xs) =
  case nonEmpty xs of
    Nothing -> x >< (RUnit :# locEnd l)
    Just xs' -> x >< rawTuple xs'

instance Pretty (Raw l) where
  pretty (RSymbol (Symbol s) :# _) = pretty s
  pretty (RTsSymbol (Symbol s) n :# _) = pretty s <> "@" <> pretty n
  pretty (RS "def" :. r)
    | Just rs <- maybeList r =
        parens ("def" <+> (align . sep $ pretty <$> rs))
  pretty r | Just rs <- retuple r = brackets (align . sep $ pretty <$> rs)
    where
      retuple (RS "cons" :. q :. RU :. RU) = Just [q]
      retuple (RS "cons" :. q :. qs :. RU) = Just (q :) <*> retuple qs
      retuple _ = Nothing
  pretty (RS "quote" :. q :. RU) = "'" <> pretty q
  pretty (RS "quasiquote" :. q :. RU) = "`" <> pretty q
  pretty (RS "unquote" :. q :. RU) = "," <> pretty q
  pretty (RS "unquote-splicing" :. q :. RU) = ",@" <> pretty q
  pretty r | Just rs <- maybeList r = parens (align . sep $ pretty <$> rs)
  pretty (RPair a b :# _) = parens (pretty a <> " . " <> pretty b)
  pretty (RUnit :# _) = "()"
