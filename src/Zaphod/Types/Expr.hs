{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Expr where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import qualified GHC.Exts (IsList (..))
import qualified GHC.Show (Show (..))
import Zaphod.Types.Class
import Zaphod.Types.Location
import Zaphod.Types.Wrapper

data ExprBug
  = EqUndefined
  | StripTypeSpecial
  | NotListZType ZType
  | NotListTyped (Typed ())
  | NotListUntyped (Untyped ())
  deriving (Show)

instance Exception ExprBug

data NativeException
  = TypeMismatch Text (Typed ()) Text
  deriving (Show)

data Expr t h
  = EType ZType
  | EUnit
  | ESymbol Symbol t
  | ELambda Variable h Environment t
  | EImplicit Variable h Environment t
  | EMacro Variable h t
  | EApply h h t
  | EPair h h t
  | EAnnotation h ZType
  | EQuote h t
  | ENative1 Native1 t
  | ENative2 Native2 t
  | ENativeIO NativeIO t
  | ESpecial t
  deriving (Show, Eq, Functor, Foldable, Traversable)

type Untyped = LocB Expr ()

type Typed = LocB Expr ZType

data ZType
  = ZType Int
  | ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal ZType
  | ZFunction ZType ZType
  | ZImplicit ZType ZType
  | ZSymbol
  | ZPair ZType ZType
  | ZValue (Typed ())
  | ZUntyped (Untyped ())
  | ZAny
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

  fromList = foldr ZPair ZUnit

  toList ZUnit = []
  toList (ZPair l r) = l : GHC.Exts.toList r
  toList r = bug (NotListZType r)

stripType :: Typed l -> Untyped l
stripType = first (const ())

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
  render (ZImplicit a b) = render a <> " => " <> render b
  render ZSymbol = "Symbol"
  render p@(ZPair l r) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (ZValue x) = "{" <> render' x <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"
  render ZAny = "Any"

newtype Native1 = Native1 (Typed () -> Either NativeException (Typed ()))

instance Eq Native1 where
  _ == _ = bug EqUndefined

instance Show Native1 where
  show _ = "Native1 <native1>"

newtype Native2 = Native2 (Typed () -> Typed () -> Either NativeException (Typed ()))

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

deriveBifunctor ''Expr
deriveBifoldable ''Expr
deriveBitraversable ''Expr

instance MaybeList (LocB Expr l t) where
  isList (EUnit :@ _) = True
  isList (EPair _ r _ :@ _) = isList r
  isList _ = False

  maybeList (EUnit :@ _) = Just []
  maybeList (EPair l r _ :@ _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance (Monoid l) => IsString (Untyped l) where
  fromString s = ESymbol (fromString s) () :@ mempty

instance (Monoid l) => IsList (Untyped l) where
  type Item (Untyped l) = Untyped l

  fromList [] = EUnit :@ mempty
  fromList (x : xs) =
    let xs' = fromList xs
     in EPair x xs' () :@ (location x <> location xs')

  toList (EUnit :@ _) = []
  toList (EPair l r _ :@ _) = l : GHC.Exts.toList r
  toList e = bug (NotListUntyped $ stripLocation e)

instance (Monoid l) => IsList (Typed l) where
  type Item (Typed l) = Typed l

  fromList [] = EUnit :@ mempty
  fromList (x : xs) =
    let xs' = fromList xs
     in EPair x xs' (ZPair (exprType x) (exprType xs')) :@ (location x <> location xs')

  toList (EUnit :@ _) = []
  toList (EPair l r _ :@ _) = l : GHC.Exts.toList r
  toList e = bug (NotListTyped $ stripLocation e)

exprType :: Typed l -> ZType
exprType (EType (ZType n) :@ _) = ZType (n + 1)
exprType (EType _ :@ _) = ZType 0
exprType (EUnit :@ _) = ZUnit
exprType (ELambda _ _ _ t :@ _) = t
exprType (EImplicit _ _ _ t :@ _) = t
exprType (EMacro _ _ t :@ _) = t
exprType (EAnnotation _ t :@ _) = t
exprType (ESymbol _ t :@ _) = t
exprType (EPair _ _ t :@ _) = t
exprType (EApply _ _ t :@ _) = t
exprType (EQuote _ t :@ _) = t
exprType (ENative1 _ t :@ _) = t
exprType (ENative2 _ t :@ _) = t
exprType (ENativeIO _ t :@ _) = t
exprType (ESpecial t :@ _) = t

instance Render (Untyped l) where
  render (EType z :@ _) = "[" <> render z <> "]"
  render (EUnit :@ _) = "()"
  render (ESymbol t () :@ _) = render t
  render (ELambda _ _ _ () :@ _) = "<lambda>"
  render (EImplicit x e _ () :@ _) = "(implicit " <> render x <> " " <> render e <> ")"
  render (EMacro x e () :@ _) = "(macro " <> render x <> " " <> render e <> ")"
  render p@(EPair l r () :@ _) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (EAnnotation e z :@ _) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply f xs () :@ l) = render (EPair f xs () :@ l)
  render (EQuote t () :@ _) = "'" <> render t
  render (ENative1 _ () :@ _) = "<native1>"
  render (ENative2 _ () :@ _) = "<native2>"
  render (ENativeIO _ () :@ _) = "<nativeIO>"
  render (ESpecial () :@ _) = "<special>"

instance Render (Typed l) where
  render (EType (ZValue e) :@ _) = "[{" <> render' e <> "}] : Type"
  render (EType z :@ _) = "[" <> render z <> "] : Type"
  render (EUnit :@ _) = "() : ()"
  render (ESymbol t z :@ _) = render t <> " : " <> render z
  render (ELambda _ _ _ z :@ _) = "<lambda> : " <> render z
  render (EImplicit x e _ z :@ _) = "(implicit " <> render x <> " " <> render e <> ") : " <> render z
  render (EMacro x e z :@ _) = "(macro " <> render x <> " " <> render e <> ") : " <> render z
  render p@(EPair l r z :@ _) =
    case maybeList $ stripType p of
      Just xs -> render xs <> " : " <> render z
      Nothing -> render (stripType l, stripType r) <> " : " <> render z
  render (EAnnotation e z :@ _) = "(" <> render' e <> " : " <> render z <> ")"
  render (EApply f x z :@ l) = render (EPair (stripType f) (stripType x) () :@ l) <> " : " <> render z
  render (EQuote x z :@ _) = "'" <> render' x <> " : " <> render z
  render (ENative1 _ z :@ _) = "<native1> : " <> render z
  render (ENative2 _ z :@ _) = "<native2> : " <> render z
  render (ENativeIO _ z :@ _) = "<nativeIO> : " <> render z
  render (ESpecial z :@ _) = "<special> : " <> render z

unwrapType :: Typed l -> ZType
unwrapType (EType z :@ _) = z
unwrapType e = ZValue $ stripLocation e

setType :: ZType -> Typed l -> Typed l
setType _ (EUnit :@ l) = EUnit :@ l
setType _ (EType z :@ l) = EType z :@ l
setType z (ESymbol s _ :@ l) = ESymbol s z :@ l
setType z (ELambda x e env _ :@ l) = ELambda x e env z :@ l
setType z (EImplicit x e env _ :@ l) = EImplicit x e env z :@ l
setType z (EMacro x e _ :@ l) = EMacro x e z :@ l
setType z (EApply f xs _ :@ l) = EApply f xs z :@ l
setType z (EPair x y _ :@ l) = EPair x y z :@ l
setType z (EAnnotation e _ :@ l) = EAnnotation e z :@ l
setType z (EQuote q _ :@ l) = EQuote q z :@ l
setType z (ENative1 n _ :@ l) = ENative1 n z :@ l
setType z (ENative2 n _ :@ l) = ENative2 n z :@ l
setType z (ENativeIO n _ :@ l) = ENativeIO n z :@ l
setType z (ESpecial _ :@ l) = ESpecial z :@ l
