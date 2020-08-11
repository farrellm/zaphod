{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types where

import qualified Data.Text as T
import Lens.Micro.TH (makeLenses)
import Prelude hiding (show)

data TypesError
  = ListNotAList
  deriving (Show)

instance Exception TypesError

class Render a where
  render :: a -> Text

newtype Keyword = Keyword {getKeyword :: Text}
  deriving (Show, Eq, Ord)

instance Render Keyword where
  render k = ":" <> getKeyword k

newtype Universal = Universal {getUniversal :: Text}
  deriving (Show, Eq, Ord)

instance Render Universal where
  render = getUniversal

newtype Existential = Existential {getExistential :: Text}
  deriving (Show, Eq, Ord)

instance Render Existential where
  render = getExistential

newtype Variable = Variable {getVariable :: Text}
  deriving (Show, Eq, Ord)

instance Render Variable where
  render = getVariable

data ZType
  = ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZSymbol
  deriving (Show, Eq)

instance {-# OVERLAPPING #-} Render ZType where
  render ZUnit = "()"
  render (ZUniversal u) = "u" <> render u
  render (ZExistential e) = "e" <> render e
  render (ZForall u e) = "∀" <> render u <> "." <> render e
  render (ZFunction a b) = render a <> " -> " <> render b
  render ZSymbol = "Symbol"

data Expr t
  = EUnit
  | ESymbol Text t
  | ELambda Variable (Expr t) t
  | EPair (Expr t) (Expr t) t
  | EAnnotation (Expr t) ZType
  deriving (Show, Functor, Foldable, Traversable)

type Untyped = Expr ()

type Typed = Expr ZType

isList :: Expr a -> Bool
isList EUnit = True
isList (EPair _ EUnit _) = True
isList (EPair _ (EPair _ r _) _) = isList r
isList _ = False

instance Render Untyped where
  render EUnit = "()"
  render (ESymbol t ()) = t
  render (ELambda x e ()) = "(\\" <> render x <> " . " <> render e <> ")"
  render p@(EPair l r ())
    | isList p = "(" <> render l <> go r
    | otherwise = "(" <> render l <> " . " <> render r <> ")"
    where
      go EUnit = ")"
      go (EPair a b ()) = " " <> render a <> go b
      go _ = bug ListNotAList
  render (EAnnotation e z) = "(" <> render e <> " : " <> render z <> ")"

instance Render Typed where
  render EUnit = "()"
  render (ESymbol t z) = t <> " : " <> render z
  render (ELambda x e z) = "(\\" <> render x <> " . " <> render e <> ")" <> " :: " <> render z
  render p@(EPair l r z)
    | isList p = "(" <> render l <> go r
    | otherwise = "(" <> render l <> " . " <> render r <> ")"
    where
      go EUnit = ")" <> " : " <> render z
      go (EPair a b _) = " " <> render a <> go b
      go _ = bug ListNotAList
  render (EAnnotation e z) = "(" <> render e <> " : " <> render z <> ")"

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

instance Render ContextEntry where
  render (CUnsolved a) = render a
  render (CSolved a b) = render a <> "=" <> render b
  render (CMarker a) = ">" <> render a
  render (CUniversal a) = render a
  render (CVariable a b) = render a <> ":" <> render b

newtype Context = Context [ContextEntry]
  deriving (Show)

instance Render Context where
  render (Context cs) = "Context [" <> T.intercalate ", " (render <$> cs) <> "]"

data Hole = Hole Existential [ContextEntry]
  deriving (Show)

data ZState = ZState
  { _context :: Context,
    _existentialData :: Char
  }
  deriving (Show)

makeLenses ''ZState

instance (Render a, Render b) => Render (a, b) where
  render (a, b) = "(" <> render a <> ", " <> render b <> ")"
