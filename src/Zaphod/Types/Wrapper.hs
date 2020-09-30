{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Zaphod.Types.Wrapper where

import Zaphod.Types.Class

newtype Symbol = Symbol {getSymbol :: Text}
  deriving (Show, Eq, Ord, IsString)

instance Render Symbol where
  render = getSymbol
  {-# INLINE render #-}

newtype Universal = Universal {getUniversal :: Symbol}
  deriving (Show, Eq, Ord)

instance Render Universal where
  render = getSymbol . getUniversal
  {-# INLINE render #-}

newtype Existential = Existential {getExistential :: Symbol}
  deriving (Show, Eq, Ord)

instance Render Existential where
  render = getSymbol . getExistential
  {-# INLINE render #-}

newtype Variable = Variable {getVariable :: Symbol}
  deriving (Show, Eq, Ord)

instance Render Variable where
  render = getSymbol . getVariable
  {-# INLINE render #-}
