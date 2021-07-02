{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types.Location where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Text.Megaparsec (SourcePos)
import Zaphod.Types.Class

data LocF f l = f (LocF f l) :# l
  deriving (Functor, Foldable, Traversable)

data LocB f t l = f t (LocB f t l) :@ l
  deriving (Functor, Foldable, Traversable)

deriveBifunctor ''LocB
deriveBifoldable ''LocB
deriveBitraversable ''LocB

instance Location l => HasLocation (LocB e t l) where
  type Value (LocB e t l) = e t (LocB e t l)
  type Locat (LocB e t l) = l
  location (_ :@ l) = l
  value (v :@ _) = v
  withLocation = (:@)

newtype LocU f t = LocU (f t (LocU f t))

instance Bifunctor f => Functor (LocU f) where
  fmap f (LocU l) = LocU (bimap f (f <$>) l)

instance Bifoldable f => Foldable (LocU f) where
  foldMap f (LocU l) = bifoldMap f (foldMap f) l

instance Bitraversable f => Traversable (LocU f) where
  traverse f (LocU l) = LocU <$> bitraverse f (traverse f) l

instance HasLocation (LocU e t) where
  type Value (LocU e t) = e t (LocU e t)
  type Locat (LocU e t) = ()
  location _ = ()
  value (LocU v) = v
  withLocation v () = LocU v

errorLocation :: (Functor f, MonadError (f a) m) => a -> ExceptT (f ()) m b -> m b
errorLocation a x = do
  e <- runExceptT x
  case e of
    Left err -> throwError (a <$ err)
    Right res -> pure res

data Loc = Loc SourcePos SourcePos
  deriving (Show)

instance Semigroup Loc where
  Loc a _ <> Loc _ b = Loc a b

instance Location Loc where
  locBegin (Loc a _) = Loc a a
  locEnd (Loc _ b) = Loc b b
