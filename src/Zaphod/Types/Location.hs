{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Zaphod.Types.Location where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Zaphod.Types.Class

data LocF f l = f (LocF f l) :# l
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f (LocF f l)), Show l) => Show (LocF f l)

deriving instance (Eq (f (LocF f l)), Eq l) => Eq (LocF f l)

instance HasLocation (LocF f) where
  location (_ :# l) = l

data LocB f t l = f t (LocB f t l) :@ l
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f t (LocB f t l)), Show l) => Show (LocB f t l)

deriving instance (Eq (f t (LocB f t l)), Eq l) => Eq (LocB f t l)

deriveBifunctor ''LocB
deriveBifoldable ''LocB
deriveBitraversable ''LocB

instance HasLocation (LocB f t) where
  location (_ :@ l) = l
