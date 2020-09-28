{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Raw where

import qualified GHC.Exts (IsList (..))
import Zaphod.Types.Class
import Zaphod.Types.Wrapper

data TypesBug
  = NotList
  deriving (Show)

instance Exception TypesBug

data Raw l
  = RUnit l
  | RSymbol Symbol l
  | RPair (Raw l) (Raw l) l
  deriving (Show, Eq, Functor)

instance HasLocation (Raw l) where
  type Loc (Raw l) = l
  type UnitLoc (Raw l) = Raw ()

  location (RUnit l) = l
  location (RSymbol _ l) = l
  location (RPair _ _ l) = l

  stripLocation r = const () <$> r
  setLocation l r = const l <$> r

instance (Monoid l) => IsString (Raw l) where
  fromString s = RSymbol (fromString s) mempty

instance Render (Raw l) where
  render (RUnit _) = "()"
  render (RSymbol s _) = render s
  render p@(RPair l r _) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)

instance MaybeList (Raw l) where
  isList (RUnit _) = True
  isList (RPair _ r _) = isList r
  isList _ = False

  maybeList (RUnit _) = Just []
  maybeList (RPair l r _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance (Monoid l) => IsList (Raw l) where
  type Item (Raw l) = Raw l

  fromList [] = RUnit mempty
  fromList (x : xs) =
    let y = fromList xs
     in RPair x y (location x <> location y)

  toList (RUnit _) = []
  toList (RPair l r _) = l : GHC.Exts.toList r
  toList _ = bug NotList
