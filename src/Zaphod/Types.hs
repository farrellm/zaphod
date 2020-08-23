{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod.Types where

import qualified Data.Text as T
import qualified GHC.Show
import Lens.Micro.TH (makeLenses)

debug :: Bool
debug = False

traceM' :: Applicative f => Text -> f ()
traceM' x = do
  when debug . traceM $ toString x

data TypesBug = EqUndefined
  deriving (Show)

instance Exception TypesBug

type Environment = Map Symbol Typed

class Render a where
  render :: a -> Text

class MaybeList a where
  isList :: a -> Bool
  fromList' :: [a] -> a
  maybeList :: a -> Maybe [a]

instance Render a => Render [a] where
  render xs = "(" <> T.intercalate " " (render <$> xs) <> ")"
  {-# INLINE render #-}

instance (Render a, Render b) => Render (a, b) where
  render (l, r) = "(" <> render l <> " . " <> render r <> ")"
  {-# INLINE render #-}

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

data Raw
  = RUnit
  | RSymbol Symbol
  | RPair Raw Raw
  deriving (Show, Eq)

instance IsString Raw where
  fromString s = RSymbol (fromString s)

instance Render Raw where
  render RUnit = "()"
  render (RSymbol s) = render s
  render p@(RPair l r) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)

instance MaybeList Raw where
  isList RUnit = True
  isList (RPair _ RUnit) = True
  isList (RPair _ r) = isList r
  isList _ = False

  fromList' [] = RUnit
  fromList' (x : xs) = RPair x (fromList' xs)

  maybeList RUnit = Just []
  maybeList (RPair l r) = (l :) <$> maybeList r
  maybeList _ = Nothing

data ZType
  = ZType Int
  | ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZSymbol
  | ZPair ZType ZType
  | ZValue (Expr ZType)
  | ZUntyped (Expr ())
  deriving (Show, Eq)

instance MaybeList ZType where
  isList ZUnit = True
  isList (ZPair _ ZUnit) = True
  isList (ZPair _ r) = isList r
  isList _ = False

  fromList' [] = ZUnit
  fromList' (x : xs) = ZPair x (fromList' xs)

  maybeList ZUnit = Just []
  maybeList (ZPair l r) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance Render ZType where
  render (ZType 0) = "Type"
  render (ZType n) = "Type " <> show n
  render ZUnit = "()"
  render (ZUniversal u) = "u" <> render u
  render (ZExistential e) = "∃" <> render e
  render (ZForall u e) = "∀" <> render u <> "." <> render e
  render (ZFunction a b) = render a <> " -> " <> render b
  render ZSymbol = "Symbol"
  render p@(ZPair l r) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (ZValue x) = "{" <> render x <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"

data Expr t
  = EType ZType
  | EUnit
  | ESymbol Symbol t
  | ELambda Variable (Expr t) Environment t
  | ELambda' [Variable] (Expr t) Environment t
  | EApply (Expr t) [Expr t] t
  | EPair (Expr t) (Expr t) t
  | EAnnotation (Expr t) ZType
  | EQuote (Expr t) t
  | ENative1 Native1 t
  | ENative2 Native2 t
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype Native1 = Native1 (Typed -> Typed)

instance Eq Native1 where
  _ == _ = bug EqUndefined

instance Show Native1 where
  show _ = "Native1 <native1>"

newtype Native2 = Native2 (Typed -> Typed -> Typed)

instance Eq Native2 where
  _ == _ = bug EqUndefined

instance Show Native2 where
  show _ = "Native2 <native2>"

type Untyped = Expr ()

type Typed = Expr ZType

instance IsString Untyped where
  fromString s = ESymbol (fromString s) ()

exprIsList :: Expr a -> Bool
exprIsList EUnit = True
exprIsList (EPair _ EUnit _) = True
exprIsList (EPair _ r _) = exprIsList r
exprIsList _ = False

exprMaybeList :: Expr a -> Maybe [Expr a]
exprMaybeList EUnit = Just []
exprMaybeList (EPair l r _) = (l :) <$> exprMaybeList r
exprMaybeList _ = Nothing

instance MaybeList Untyped where
  isList = exprIsList
  {-# INLINE isList #-}
  maybeList = exprMaybeList
  {-# INLINE maybeList #-}
  fromList' [] = EUnit
  fromList' (x : xs) = EPair x (fromList' xs) ()

instance MaybeList Typed where
  isList = exprIsList
  {-# INLINE isList #-}
  maybeList = exprMaybeList
  {-# INLINE maybeList #-}
  fromList' [] = EUnit
  fromList' (x : xs) =
    let xs' = fromList' xs
     in EPair x xs' (ZPair (exprType x) (exprType xs'))

exprType :: Typed -> ZType
exprType (EType (ZType n)) = ZType (n + 1)
exprType (EType _) = ZType 0
exprType EUnit = ZUnit
exprType (ELambda _ _ _ t) = t
exprType (ELambda' _ _ _ t) = t
exprType (EAnnotation _ t) = t
exprType (ESymbol _ t) = t
exprType (EPair _ _ t) = t
exprType (EApply _ _ t) = t
exprType (EQuote _ t) = t
exprType (ENative1 _ t) = t
exprType (ENative2 _ t) = t

stripType :: Typed -> Untyped
stripType (EType n) = EType n
stripType EUnit = EUnit
stripType (ESymbol s _) = ESymbol s ()
stripType (ELambda x e n _) = ELambda x (stripType e) n ()
stripType (ELambda' xs e n _) = ELambda' xs (stripType e) n ()
stripType (EApply f xs _) = EApply (stripType f) (stripType <$> xs) ()
stripType (EPair x y _) = EPair (stripType x) (stripType y) ()
stripType (EAnnotation x t) = EAnnotation (stripType x) t
stripType (EQuote x _) = EQuote (stripType x) ()
stripType (ENative1 f _) = ENative1 f ()
stripType (ENative2 f _) = ENative2 f ()

instance Render Untyped where
  render (EType z) = "[" <> render z <> "]"
  render EUnit = "()"
  render (ESymbol t ()) = render t
  render (ELambda x e _ ()) = "(\\" <> render x <> " " <> render e <> ")"
  render (ELambda' xs e _ ()) = "(\\" <> render xs <> " " <> render e <> ")"
  render p@(EPair l r ()) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (EAnnotation e z) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply f xs ()) = render (f : xs)
  render (EQuote t ()) = "'" <> render t
  render (ENative1 _ ()) = "<native1>"
  render (ENative2 _ ()) = "<native2>"

render' :: Typed -> Text
render' = render . stripType

instance Render Typed where
  render (EType z) = "[" <> render z <> "]"
  render EUnit = "() : ()"
  render (ESymbol t z) = render t <> " : " <> render z
  render (ELambda x e _ z) = "(\\" <> render x <> " " <> render' e <> ") : " <> render z
  render (ELambda' xs e _ z) = "(\\" <> render xs <> " " <> render' e <> ") : " <> render z
  render p@(EPair l r z) =
    case maybeList $ stripType p of
      Just xs -> render xs <> " : " <> render z
      Nothing -> render (stripType l, stripType r) <> " : " <> render z
  render (EAnnotation e z) = "(" <> render' e <> " : " <> render z <> ")"
  render (EApply f xs z) = render (stripType <$> f : xs) <> " : " <> render z
  render (EQuote x z) = "'" <> render' x <> " : " <> render z
  render (ENative1 _ z) = "<native1> : " <> render z
  render (ENative2 _ z) = "<native2> : " <> render z

unwrapType :: Typed -> ZType
unwrapType (EType z) = z
unwrapType e = ZValue e

unwrapType' :: Untyped -> ZType
unwrapType' (EType z) = z
unwrapType' e = ZUntyped e

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
    _environment :: Environment,
    _existentialData :: Char
  }
  deriving (Show)

makeLenses ''ZState
