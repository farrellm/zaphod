{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Zaphod.Types.Raw where

import Zaphod.Types.Class (Location (..), Magma (..), MaybeList (..), Render (..))
import Zaphod.Types.Location (LocF (..), LocU (..))
import Zaphod.Types.Wrapper (Symbol)

data RawF k
  = RUnit
  | RSymbol Symbol
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

pattern RU :: Raw l
pattern RU <- RUnit :# _

pattern RS :: Symbol -> Raw l
pattern RS s <- RSymbol s :# _

pattern (:.) :: Raw l -> Raw l -> Raw l
pattern (:.) x y <- RPair x y :# _

infixr 5 :.

{-# COMPLETE RU, RS, (:.) #-}

rawTuple :: Location l => NonEmpty (Raw l) -> Raw l
rawTuple (x@(_ :# l) :| xs) =
  case nonEmpty xs of
    Nothing -> x >< (RUnit :# locEnd l)
    Just xs' -> x >< rawTuple xs'
