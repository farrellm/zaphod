{-# LANGUAGE TypeApplications #-}

module Zaphod.Types.Location where

import Data.MonoTraversable (Element, MonoFunctor (..))
import Text.Megaparsec (SourcePos)
import Zaphod.Types.Class (Injection (..), Location (..), Projection (..))

newtype LocU f = LocU (f (LocU f))

data LocF f l = f (LocF f l) :# l
  deriving (Functor, Foldable, Traversable)

data LocB f z l = f (LocB f z l) :@ (l, z (LocB f z l))
  deriving (Functor, Foldable, Traversable)

data LocA f z = f (LocA f z) :$ z (LocA f z)

data UnitF a = UnitF
  deriving (Functor, Foldable, Traversable, Eq)

instance (Functor f) => Projection (LocA f z) (LocU f) where
  project (x :$ _) = LocU $ project <$> x

data Loc = Loc SourcePos SourcePos
  deriving (Show)

instance Semigroup Loc where
  Loc a _ <> Loc _ b = Loc a b

instance Location Loc where
  locBegin (Loc a _) = Loc a a
  locEnd (Loc _ b) = Loc b b

setLocation :: (Functor f, Functor z) => l -> LocA f z -> LocB f z l
setLocation l (x :$ t) = (setLocation l <$> x) :@ (l, setLocation l <$> t)

instance (Functor f) => Projection (LocF f l) (LocU f) where
  project (x :# _) = LocU (project <$> x)

instance (Functor f, Functor z) => Projection (LocB f z l) (LocF f l) where
  project (x :@ (l, _)) = (project <$> x) :# l

instance (Functor f, Functor z) => Projection (LocB f z l) (LocA f z) where
  project (x :@ (_, t)) = (project <$> x) :$ (project <$> t)

instance (Functor f, Functor z) => Projection (LocB f z l) (LocU f) where
  project = project @(LocA f z) . project

instance (Functor f, Functor z, Monoid l) => Injection (LocA f z) (LocB f z l) where
  embed (x :$ z) = (embed <$> x) :@ (mempty, embed <$> z)

type instance Element (LocB f z l) = z (LocB f z l)

instance (Functor f) => MonoFunctor (LocB f z l) where
  omap f (x :@ (l, z)) = (omap f <$> x) :@ (l, f z)
