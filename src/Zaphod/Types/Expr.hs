{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Expr where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import qualified GHC.Exts (IsList (..))
import qualified GHC.Exts as GE
import qualified GHC.Show (Show (..))
import Relude.Extra.Map
import Zaphod.Types.Class
import Zaphod.Types.Location
import Zaphod.Types.Wrapper

data ExprBug
  = EqUndefined
  | StripTypeSpecial
  | ListEmpty
  | NotListZType ZType
  | NotListTyped (Typed ())
  | NotListUntyped (Untyped ())
  deriving (Show)

instance Exception ExprBug

data NativeException l
  = TypeMismatch Text (Typed l) Text
  deriving (Show, Functor)

newtype Environment e = Environment {getEnvironment :: Map Symbol e}
  deriving (Show, Eq, Functor, Foldable, Traversable, Semigroup, Monoid)

instance StaticMap (Environment e) where
  type Key (Environment e) = Symbol
  type Val (Environment e) = e
  size = size . getEnvironment
  lookup k = lookup k . getEnvironment
  member v = member v . getEnvironment

instance DynamicMap (Environment e) where
  insert k v = Environment . insert k v . getEnvironment
  insertWith f k v = Environment . insertWith f k v . getEnvironment
  delete k = Environment . delete k . getEnvironment
  alter f k = Environment . alter f k . getEnvironment

instance IsList (Environment e) where
  type Item (Environment e) = (Symbol, e)
  fromList = Environment . fromList
  toList = GE.toList . getEnvironment

data Expr t l
  = EType ZType
  | EUnit
  | ESymbol Symbol t
  | ELambda1 Variable (LocB Expr t l) (Environment (Typed l)) t
  | ELambdaN [Variable] (LocB Expr t l) (Environment (Typed l)) t
  | EImplicit Variable (LocB Expr t l) (Environment (Typed l)) t
  | EMacro1 Variable (LocB Expr t l) t
  | EMacroN [Variable] (LocB Expr t l) t
  | EApply1 (LocB Expr t l) (LocB Expr t l) t
  | EApplyN (LocB Expr t l) (NonEmpty (LocB Expr t l)) t
  | EPair (LocB Expr t l) (LocB Expr t l) t
  | EAnnotation (LocB Expr t l) ZType
  | EQuote (LocB Expr t l) t
  | ENative Native t
  | ENative' Native' t
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
  render (ZValue x) = "{" <> render (stripType x) <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"
  render ZAny = "Any"

newtype Native = Native (forall l. Typed l -> Either (NativeException l) (Typed ()))

instance Eq Native where
  _ == _ = bug EqUndefined

instance Show Native where
  show _ = "Native <native>"

newtype Native' = Native' (forall l. (Semigroup l, Location l) => Typed l -> Either (NativeException l) (Typed l))

instance Eq Native' where
  _ == _ = bug EqUndefined

instance Show Native' where
  show _ = "Native' <native>"

newtype NativeIO = NativeIO (IO (Typed ()))

instance Eq NativeIO where
  _ == _ = bug EqUndefined

instance Show NativeIO where
  show _ = "NativeIO <nativeIO>"

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

instance (Semigroup l, Location l) => IsList (Untyped l) where
  type Item (Untyped l) = Untyped l

  fromList [] = bug ListEmpty
  fromList [x] = EPair x (EUnit :@ getEnd (location x)) () :@ location x
  fromList (x : xs) =
    let xs' = fromList xs
     in EPair x xs' () :@ (location x <> location xs')

  toList (EUnit :@ _) = []
  toList (EPair l r _ :@ _) = l : GHC.Exts.toList r
  toList e = bug (NotListUntyped $ stripLocation e)

instance (Semigroup l, Location l) => IsList (Typed l) where
  type Item (Typed l) = Typed l

  fromList [] = bug ListEmpty
  fromList [x] = EPair x (EUnit :@ getEnd (location x)) (ZPair (exprType x) ZUnit) :@ location x
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
exprType (ELambda1 _ _ _ t :@ _) = t
exprType (ELambdaN _ _ _ t :@ _) = t
exprType (EImplicit _ _ _ t :@ _) = t
exprType (EMacro1 _ _ t :@ _) = t
exprType (EMacroN _ _ t :@ _) = t
exprType (EAnnotation _ t :@ _) = t
exprType (ESymbol _ t :@ _) = t
exprType (EPair _ _ t :@ _) = t
exprType (EApply1 _ _ t :@ _) = t
exprType (EApplyN _ _ t :@ _) = t
exprType (EQuote _ t :@ _) = t
exprType (ENative _ t :@ _) = t
exprType (ENative' _ t :@ _) = t
exprType (ENativeIO _ t :@ _) = t
exprType (ESpecial t :@ _) = t

instance Render (Untyped l) where
  render (EType z :@ _) = "[" <> render z <> "]"
  render (EUnit :@ _) = "()"
  render (ESymbol t () :@ _) = render t
  render (ELambda1 _ _ _ () :@ _) = "<lambda>"
  render (ELambdaN _ _ _ () :@ _) = "<lambda>"
  render (EImplicit _ _ _ () :@ _) = "<implicit>"
  render (EMacro1 x e () :@ _) = "(macro " <> render x <> " " <> render e <> ")"
  render (EMacroN xs e () :@ _) = "(macro " <> render xs <> " " <> render e <> ")"
  render p@(EPair l r () :@ _) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (EAnnotation e z :@ _) = "(" <> render e <> " : " <> render z <> ")"
  render (EApply1 f x () :@ l) = render (EPair f x () :@ l)
  render (EApplyN f xs () :@ _) =
    let f' = stripLocation f
        xs' = fromNonEmpty $ fmap stripLocation xs
     in render (EPair f' xs' () :@ ())
  render (EQuote t () :@ _) = "'" <> render t
  render (ENative _ () :@ _) = "<native>"
  render (ENative' _ () :@ _) = "<native>"
  render (ENativeIO _ () :@ _) = "<nativeIO>"
  render (ESpecial () :@ _) = "<special>"

instance Render (Typed l) where
  render e = render (stripType e) <> " : " <> render (exprType e)

unwrapType :: Typed l -> ZType
unwrapType (EType z :@ _) = z
unwrapType e = ZValue $ stripLocation e

unwrapTypes :: NonEmpty (Typed l) -> ZType
unwrapTypes (y :| []) = ZPair (unwrapType y) ZUnit
unwrapTypes (y :| (z : zs)) = ZPair (unwrapType y) $ unwrapTypes (z :| zs)

unwrapUntyped :: ZType -> Untyped ()
unwrapUntyped (ZUntyped e) = e
unwrapUntyped (ZValue e) = stripType e
unwrapUntyped z = EType z :@ mempty

setType :: ZType -> Typed l -> Typed l
setType _ (EUnit :@ l) = EUnit :@ l
setType _ (EType z :@ l) = EType z :@ l
setType z (ESymbol s _ :@ l) = ESymbol s z :@ l
setType z (ELambda1 x e env _ :@ l) = ELambda1 x e env z :@ l
setType z (ELambdaN xs e env _ :@ l) = ELambdaN xs e env z :@ l
setType z (EImplicit x e env _ :@ l) = EImplicit x e env z :@ l
setType z (EMacro1 x e _ :@ l) = EMacro1 x e z :@ l
setType z (EMacroN xs e _ :@ l) = EMacroN xs e z :@ l
setType z (EApply1 f x _ :@ l) = EApply1 f x z :@ l
setType z (EApplyN f xs _ :@ l) = EApplyN f xs z :@ l
setType z (EPair x y _ :@ l) = EPair x y z :@ l
setType z (EAnnotation e _ :@ l) = EAnnotation e z :@ l
setType z (EQuote q _ :@ l) = EQuote q z :@ l
setType z (ENative n _ :@ l) = ENative n z :@ l
setType z (ENative' n _ :@ l) = ENative' n z :@ l
setType z (ENativeIO n _ :@ l) = ENativeIO n z :@ l
setType z (ESpecial _ :@ l) = ESpecial z :@ l

fromNonEmpty :: (IsList a) => NonEmpty (GHC.Exts.Item a) -> a
fromNonEmpty = fromList . toList
