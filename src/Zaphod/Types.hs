{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types where

import GHC.Show (Show (..))
import Lens.Micro.TH (makeLenses)
import Prelude hiding (show)

data TypesError
  = ListNotAList
  deriving (Show)

instance Exception TypesError

newtype Keyword = Keyword {getKeyword :: Text}
  deriving (Eq, Ord)

instance Show Keyword where
  show k = ":" <> toString (getKeyword k)

newtype Universal = Universal {getUniversal :: Text}
  deriving (Eq, Ord)

instance Show Universal where
  show = toString . getUniversal

newtype Existential = Existential {getExistential :: Text}
  deriving (Eq, Ord)

instance Show Existential where
  show = toString . getExistential

newtype Variable = Variable {getVariable :: Text}
  deriving (Eq, Ord)

instance Show Variable where
  show = toString . getVariable

data ZType
  = ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZSymbol
  deriving (Eq)

instance {-# OVERLAPPING #-} Show ZType where
  show ZUnit = "()"
  show (ZUniversal u) = "u" ++ show u
  show (ZExistential e) = "e" ++ show e
  show (ZForall u e) = "∀" ++ show u ++ "." ++ show e
  show (ZFunction a b) = show a ++ " -> " ++ show b
  show ZSymbol = "Symbol"

data Expr t
  = EUnit
  | ESymbol Text t
  | ELambda Variable (Expr t) t
  | EPair (Expr t) (Expr t) t
  | EAnnotation (Expr t) ZType
  deriving (Functor, Foldable, Traversable)

type Untyped = Expr ()

type Typed = Expr ZType

deriving instance {-# OVERLAPPABLE #-} Show t => Show (Expr t)

isList :: Expr a -> Bool
isList EUnit = True
isList (EPair _ EUnit _) = True
isList (EPair _ (EPair _ r _) _) = isList r
isList _ = False

instance {-# OVERLAPPING #-} Show Untyped where
  show EUnit = "()"
  show (ESymbol t ()) = toString t
  -- show (EVar (Variable x) ()) = toString x
  show (ELambda x e ()) = "(\\" ++ show x ++ " . " ++ show e ++ ")"
  show p@(EPair l r ())
    | isList p = "(" ++ show l ++ go r
    | otherwise = "(" ++ show l ++ " . " ++ show r ++ ")"
    where
      go EUnit = ")"
      go (EPair a b ()) = " " ++ show a ++ go b
      go _ = bug ListNotAList
  show (EAnnotation e z) = "(" ++ show e ++ " : " ++ show z ++ ")"

instance {-# OVERLAPPING #-} Show Typed where
  show EUnit = "()"
  show (ESymbol t z) = toString t ++ " :: " ++ show z
  -- show (EVar (Variable x) z) = toString x ++ " :: " ++ show z
  show (ELambda x e z) = "(\\" ++ show x ++ " . " ++ show e ++ ")" ++ " :: " ++ show z
  show p@(EPair l r z)
    | isList p = "(" ++ show l ++ go r
    | otherwise = "(" ++ show l ++ " . " ++ show r ++ ")"
    where
      go EUnit = ")" ++ " :: " ++ show z
      go (EPair a b _) = " " ++ show a ++ go b
      go _ = bug ListNotAList
  show (EAnnotation e z) = "(" ++ show e ++ " : " ++ show z ++ ")"

data LookupResult
  = RSolved ZType
  | RUnsolved
  | RMissing
  deriving (Show)

data ContextEntry
  = CUnsolved Existential
  | CSolved Existential ZType
  | CMarker Existential
  | CUniversal Universal
  | CVariable Variable ZType
  deriving (Show)

newtype Context = Context [ContextEntry]
  deriving (Show)

data Hole = Hole Existential [ContextEntry]
  deriving (Show)

data ZState = ZState
  { _context :: Context,
    _existentialData :: Char
  }
  deriving (Show)

makeLenses ''ZState
