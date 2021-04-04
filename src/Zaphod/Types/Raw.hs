{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Raw where

import qualified GHC.Exts (IsList (..))
import Zaphod.Types.Class
import Zaphod.Types.Location
import Zaphod.Types.Wrapper

data RawBug
  = NotListRaw (Raw ())
  | RawEmptyList
  deriving (Show)

instance Exception RawBug

data Raw' k
  = RUnit
  | RSymbol Symbol
  | RPair k k
  deriving (Show, Eq, Functor)

type Raw = LocF Raw'

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

instance (Semigroup l, Location l) => IsList (Raw l) where
  type Item (Raw l) = Raw l

  fromList [] = bug RawEmptyList
  fromList [x] =
    let l = location x
     in RPair x (RUnit :# getEnd l) :# l
  fromList (x : xs) =
    let xs' = fromList xs
     in RPair x xs' :# (location x <> location xs')

  toList (RUnit :# _) = []
  toList (RPair l r :# _) = l : GHC.Exts.toList r
  toList r = bug (NotListRaw $ stripLocation r)

pattern RU :: Raw l
pattern RU <- RUnit :# _

pattern RS :: Symbol -> Raw l
pattern RS s <- RSymbol s :# _

pattern (:.) :: Raw l -> Raw l -> Raw l
pattern (:.) x y <- RPair x y :# _

infixr 5 :.

{-# COMPLETE RU, RS, (:.) #-}
