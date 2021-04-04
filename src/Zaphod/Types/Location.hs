{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Zaphod.Types.Location where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Text.Megaparsec (SourcePos)
import Zaphod.Types.Class

data LocF f l = f (LocF f l) :# l
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f (LocF f l)), Show l) => Show (LocF f l)

deriving instance (Eq (f (LocF f l)), Eq l) => Eq (LocF f l)

instance HasLocation (LocF f) where
  location (_ :# l) = l

data LocB f t l = f t l :@ l
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f t l), Show l) => Show (LocB f t l)

instance Eq (f t l) => Eq (LocB f t l) where
  a :@ _ == b :@ _ = a == b

deriveBifunctor ''LocB
deriveBifoldable ''LocB
deriveBitraversable ''LocB

instance HasLocation (LocB f t) where
  location (_ :@ l) = l

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
  getBegin (Loc a _) = Loc a a
  getEnd (Loc _ b) = Loc b b
