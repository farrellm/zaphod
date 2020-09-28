{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Expr where

import Data.Bifunctor.TH (deriveBifunctor)
import qualified GHC.Exts (IsList (..))
import qualified GHC.Show (Show (..))
import Zaphod.Types.Class
import Zaphod.Types.Wrapper

data TypesBug
  = EqUndefined
  | StripTypeSpecial
  | NotList
  deriving (Show)

instance Exception TypesBug

data ZType
  = ZType Int
  | ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZSymbol
  | ZPair ZType ZType
  | ZValue (Expr () ZType)
  | ZUntyped (Expr () ())
  | ZTop
  deriving (Show, Eq)

instance MaybeList ZType where
  isList ZUnit = True
  isList (ZPair _ r) = isList r
  isList _ = False

  maybeList ZUnit = Just []
  maybeList (ZPair l r) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance IsList ZType where
  type Item ZType = ZType

  fromList [] = ZUnit
  fromList (x : xs) = ZPair x (fromList xs)

  toList ZUnit = []
  toList (ZPair l r) = l : GHC.Exts.toList r
  toList _ = bug NotList

stripType :: Typed l -> Untyped l
stripType = fmap (const ())

render' :: Typed l -> Text
render' = render . stripType

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
  render (ZValue x) = "{" <> render' x <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"
  render ZTop = "Top"

newtype Native1 = Native1 (Typed () -> Typed ())

instance Eq Native1 where
  _ == _ = bug EqUndefined

instance Show Native1 where
  show _ = "Native1 <native1>"

newtype Native2 = Native2 (Typed () -> Typed () -> Typed ())

instance Eq Native2 where
  _ == _ = bug EqUndefined

instance Show Native2 where
  show _ = "Native2 <native2>"

newtype NativeIO = NativeIO (IO (Typed ()))

instance Eq NativeIO where
  _ == _ = bug EqUndefined

instance Show NativeIO where
  show _ = "NativeIO <nativeIO>"

type Environment = Map Symbol (Typed ())

data Expr l t
  = EType ZType l
  | EUnit l
  | ESymbol Symbol t l
  | ELambda Variable (Expr l t) Environment t l
  | ELambda' [Variable] (Expr l t) Environment t l
  | EImplicit Variable (Expr l t) Environment t l
  | EMacro Variable (Expr l t) t l
  | EMacro' [Variable] (Expr l t) t l
  | EApply (Expr l t) [Expr l t] t l
  | EPair (Expr l t) (Expr l t) t l
  | EAnnotation (Expr l t) ZType l
  | EQuote (Expr l t) t l
  | ENative1 Native1 t l
  | ENative2 Native2 t l
  | ENativeIO NativeIO t l
  | ESpecial t l
  deriving (Show, Eq, Functor, Foldable, Traversable)

type Untyped l = Expr l ()

type Typed l = Expr l ZType

deriveBifunctor ''Expr

instance HasLocation (Expr l t) where
  type Loc (Expr l t) = l
  type UnitLoc (Expr l t) = Expr () t

  location (EType _ l) = l
  location (EUnit l) = l
  location (ESymbol _ _ l) = l
  location (ELambda _ _ _ _ l) = l
  location (ELambda' _ _ _ _ l) = l
  location (EImplicit _ _ _ _ l) = l
  location (EMacro _ _ _ l) = l
  location (EMacro' _ _ _ l) = l
  location (EApply _ _ _ l) = l
  location (EPair _ _ _ l) = l
  location (EAnnotation _ _ l) = l
  location (EQuote _ _ l) = l
  location (ENative1 _ _ l) = l
  location (ENative2 _ _ l) = l
  location (ENativeIO _ _ l) = l
  location (ESpecial _ l) = l

  stripLocation = first (const ())
  setLocation l = first (const l)

instance MaybeList (Expr l t) where
  isList (EUnit _) = True
  isList (EPair _ r _ _) = isList r
  isList _ = False

  maybeList (EUnit _) = Just []
  maybeList (EPair l r _ _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance (Monoid l) => IsString (Untyped l) where
  fromString s = ESymbol (fromString s) () mempty

instance (Monoid l) => IsList (Untyped l) where
  type Item (Untyped l) = Untyped l

  fromList [] = EUnit mempty
  fromList (x : xs) =
    let xs' = fromList xs
     in EPair x xs' () (location x <> location xs')

  toList (EUnit _) = []
  toList (EPair l r _ _) = l : GHC.Exts.toList r
  toList _ = bug NotList

instance (Monoid l) => IsList (Typed l) where
  type Item (Typed l) = Typed l

  fromList [] = EUnit mempty
  fromList (x : xs) =
    let xs' = fromList xs
     in EPair x xs' (ZPair (exprType x) (exprType xs')) (location x <> location xs')

  toList (EUnit _) = []
  toList (EPair l r _ _) = l : GHC.Exts.toList r
  toList _ = bug NotList

exprType :: Typed l -> ZType
exprType (EType (ZType n) _) = ZType (n + 1)
exprType (EType _ _) = ZType 0
exprType (EUnit _) = ZUnit
exprType (ELambda _ _ _ t _) = t
exprType (ELambda' _ _ _ t _) = t
exprType (EImplicit _ _ _ t _) = t
exprType (EMacro _ _ t _) = t
exprType (EMacro' _ _ t _) = t
exprType (EAnnotation _ t _) = t
exprType (ESymbol _ t _) = t
exprType (EPair _ _ t _) = t
exprType (EApply _ _ t _) = t
exprType (EQuote _ t _) = t
exprType (ENative1 _ t _) = t
exprType (ENative2 _ t _) = t
exprType (ENativeIO _ t _) = t
exprType (ESpecial t _) = t

instance Render (Untyped l) where
  render (EType z _) = "[" <> render z <> "]"
  render (EUnit _) = "()"
  render (ESymbol t () _) = render t
  render (ELambda _ _ _ () _) = "<lambda>"
  render (ELambda' _ _ _ () _) = "<lambda>"
  render (EImplicit x e _ () _) = "(implicit " <> render x <> " " <> render e <> ")"
  render (EMacro x e () _) = "(macro " <> render x <> " " <> render e <> ")"
  render (EMacro' xs e () _) = "(macro " <> render xs <> " " <> render e <> ")"
  render p@(EPair l r () _) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (EAnnotation e z _) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply f xs () _) = render (f : xs)
  render (EQuote t () _) = "'" <> render t
  render (ENative1 _ () _) = "<native1>"
  render (ENative2 _ () _) = "<native2>"
  render (ENativeIO _ () _) = "<nativeIO>"
  render (ESpecial () _) = "<special>"

instance Render (Typed l) where
  render (EType (ZValue e) _) = "[{" <> render' e <> "}] : Type"
  render (EType z _) = "[" <> render z <> "] : Type"
  render (EUnit _) = "() : ()"
  render (ESymbol t z _) = render t <> " : " <> render z
  render (ELambda _ _ _ z _) = "<lambda> : " <> render z
  render (ELambda' _ _ _ z _) = "<lambda> : " <> render z
  render (EImplicit x e _ z _) = "(implicit " <> render x <> " " <> render e <> ") : " <> render z
  render (EMacro x e z _) = "(macro " <> render x <> " " <> render e <> ") : " <> render z
  render (EMacro' xs e z _) = "(macro " <> render xs <> " " <> render e <> ") : " <> render z
  render p@(EPair l r z _) =
    case maybeList $ stripType p of
      Just xs -> render xs <> " : " <> render z
      Nothing -> render (stripType l, stripType r) <> " : " <> render z
  render (EAnnotation e z _) = "(" <> render' e <> " : " <> render z <> ")"
  render (EApply f xs z _) = render (stripType <$> f : xs) <> " : " <> render z
  render (EQuote x z _) = "'" <> render' x <> " : " <> render z
  render (ENative1 _ z _) = "<native1> : " <> render z
  render (ENative2 _ z _) = "<native2> : " <> render z
  render (ENativeIO _ z _) = "<nativeIO> : " <> render z
  render (ESpecial z _) = "<special> : " <> render z

unwrapType :: Typed l -> ZType
unwrapType (EType z _) = z
unwrapType e = ZValue $ stripLocation e

unwrapType' :: Untyped l -> ZType
unwrapType' (EType z _) = z
unwrapType' e = ZUntyped $ stripLocation e
