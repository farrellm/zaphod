{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types where

import qualified Data.Text as T
import Lens.Micro.TH (makeLenses)

data TypesError
  = ListNotAList
  deriving (Show)

instance Exception TypesError

class Render a where
  render :: a -> Text

newtype Symbol = Symbol {getSymbol :: Text}
  deriving (Show, Eq, Ord, IsString)

instance Render Symbol where
  render k = getSymbol k
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

data ZType
  = ZType Int
  | ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZSymbol
  | ZPair ZType ZType
  deriving (Show, Eq)

instance Render ZType where
  render (ZType 0) = "Type"
  render (ZType n) = "Type " <> show n
  render ZUnit = "()"
  render (ZUniversal u) = "u" <> render u
  render (ZExistential e) = "∃" <> render e
  render (ZForall u e) = "∀" <> render u <> "." <> render e
  render (ZFunction a b) = render a <> " -> " <> render b
  render ZSymbol = "Symbol"
  render p@(ZPair l r)
    | isZList p = "(" <> render l <> go r
    | otherwise = "(" <> render l <> " . " <> render r <> ")"
    where
      go ZUnit = ")"
      go (ZPair a b) = " " <> render a <> go b
      go _ = bug ListNotAList

data Expr t
  = EType ZType
  | EUnit
  | ESymbol Symbol t
  | ELambda Variable (Expr t) t
  | ELambda' [Variable] (Expr t) t
  | EApply (Expr t) [Expr t] t
  | EPair (Expr t) (Expr t) t
  | EAnnotation (Expr t) ZType
  deriving (Show, Functor, Foldable, Traversable)

type Untyped = Expr ()

type Typed = Expr ZType

exprType :: Typed -> ZType
exprType (EType (ZType n)) = ZType (n + 1)
exprType (EType _) = ZType 0
exprType EUnit = ZUnit
exprType (ELambda _ _ t) = t
exprType (ELambda' _ _ t) = t
exprType (EAnnotation _ t) = t
exprType (ESymbol _ t) = t
exprType (EPair _ _ t) = t
exprType (EApply _ _ t) = t

isEList :: Expr a -> Bool
isEList EUnit = True
isEList (EPair _ EUnit _) = True
isEList (EPair _ r _) = isEList r
isEList _ = False

isZList :: ZType -> Bool
isZList ZUnit = True
isZList (ZPair _ ZUnit) = True
isZList (ZPair _ r) = isZList r
isZList _ = False

makeEList :: [Untyped] -> Untyped
makeEList [] = EUnit
makeEList (x : xs) = EPair x (makeEList xs) ()

makeTypedList :: [Typed] -> Typed
makeTypedList [] = EUnit
makeTypedList (x : xs) =
  let rs = makeTypedList xs
   in EPair x rs (ZPair (exprType x) (exprType rs))

makeZList :: [ZType] -> ZType
makeZList [] = ZUnit
makeZList (z : zs) = ZPair z (makeZList zs)

maybeList :: Expr a -> Maybe [Expr a]
maybeList EUnit = Just []
maybeList (EPair l r _) = (l :) <$> maybeList r
maybeList _ = Nothing

instance Render Untyped where
  render (EType z) = render z
  render EUnit = "()"
  render (ESymbol t ()) = render t
  render (ELambda x e ()) = "(\\" <> render x <> " " <> render e <> ")"
  render (ELambda' xs e ()) = "(\\(" <> T.intercalate " " (render <$> xs) <> ") " <> render e <> ")"
  render p@(EPair l r ())
    | isEList p = "(" <> render l <> go r
    | otherwise = "(" <> render l <> " . " <> render r <> ")"
    where
      go EUnit = ")"
      go (EPair a b ()) = " " <> render a <> go b
      go _ = bug ListNotAList
  render (EAnnotation e z) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply f xs ()) = "(" <> render f <> " " <> T.intercalate " " (render <$> xs) <> ")"

instance Render Typed where
  render (EType z) = render z
  render EUnit = "()"
  render (ESymbol t z) = render t <> " : " <> render z
  render (ELambda x e z) = "(\\" <> render x <> " . " <> render e <> ") : " <> render z
  render (ELambda' xs e z) =
    "(\\(" <> T.intercalate " " (render <$> xs) <> ") . " <> render e <> ") : " <> render z
  render p@(EPair l r z)
    | isEList p = "(" <> render l <> go r
    | otherwise = "(" <> render l <> " . " <> render r <> ")"
    where
      go EUnit = ")" <> " : " <> render z
      go (EPair a b _) = " " <> render a <> go b
      go _ = bug ListNotAList
  render (EAnnotation e z) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply f xs z) =
    "(" <> render f <> " " <> T.intercalate " " (render <$> xs) <> ") : " <> render z

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

type Environment = Map Symbol Typed

data ZState = ZState
  { _context :: Context,
    _environment :: Environment,
    _existentialData :: Char
  }
  deriving (Show)

makeLenses ''ZState

instance (Render a, Render b) => Render (a, b) where
  render (a, b) = "(" <> render a <> ", " <> render b <> ")"
