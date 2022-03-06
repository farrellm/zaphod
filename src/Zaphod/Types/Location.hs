module Zaphod.Types.Location where

import Text.Megaparsec (SourcePos)
import Zaphod.Types.Class (Location (..), Projection (..))

newtype LocU f = LocU (f (LocU f))

data LocF f l = f (LocF f l) :# l
  deriving (Functor, Foldable, Traversable)

data Loc = Loc SourcePos SourcePos
  deriving (Show)

instance Semigroup Loc where
  Loc a _ <> Loc _ b = Loc a b

instance Location Loc where
  locBegin (Loc a _) = Loc a a
  locEnd (Loc _ b) = Loc b b

setLocation :: (Functor f) => l -> LocF f t -> LocF f (l, t)
setLocation l (x :# t) = (setLocation l <$> x) :# (l, t)

setLocation' :: (Functor f) => l -> LocU f -> LocF f l
setLocation' l (LocU x) = (setLocation' l <$> x) :# l

instance (Functor f) => Projection (LocF f l) (LocU f) where
  project (x :# _) = LocU (project <$> x)
