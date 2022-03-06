{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod.Types.Expr where

import qualified Data.Text as T
import qualified GHC.Exts as GE
import qualified GHC.Show (Show (..))
import Relude.Extra.Map (DynamicMap (..), StaticMap (..))
import Zaphod.Types.Class (Location (..), Magma (..), MaybeList (..), Projection (project), Render (..))
import Zaphod.Types.Location (LocF (..), LocU (..))
import Zaphod.Types.Wrapper (Existential, Symbol, Universal, Variable)

deriving instance Show (LocU Expr)

deriving instance Eq (LocU Expr)

deriving instance (Show l) => Show (LocF Expr l)

deriving instance (Eq l) => Eq (LocF Expr l)

data ExprBug
  = EqUndefined
  | StripTypeSpecial
  | ListEmpty
  | NotListZType ZType
  | NotListTyped Typed'
  | NotListUntyped Untyped'
  | UnwrapUntypedTyped (Typed ())
  deriving (Show)

instance Exception ExprBug

data NativeException l
  = TypeMismatch Text Typed' l Text
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

data Expr f
  = EType ZType
  | EUnit
  | ESymbol Symbol
  | ELambda1 Variable f (Environment f)
  | ELambdaN [Variable] f (Environment f)
  | EImplicit Variable f (Environment f)
  | EMacro1 Variable f
  | EMacroN [Variable] f
  | EApply1 f f
  | EApplyN f (NonEmpty f)
  | EPair f f
  | EAnnotation f ZType
  | EQuote f
  | ENative Native
  | ENative' Native'
  | ENativeIO NativeIO
  | ESpecial
  deriving (Show, Eq, Functor, Foldable, Traversable)

type Untyped l = LocF Expr l

type Typed l = LocF Expr (l, ZType)

type Untyped' = LocU Expr

type Typed' = LocF Expr ZType

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
  | ZUntyped Untyped'
  | ZAny
  deriving (Show, Eq)

instance Magma ZType where
  (><) = ZPair

instance MaybeList ZType where
  isList ZUnit = True
  isList (ZPair _ r) = isList r
  isList _ = False

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
  render (ZImplicit a b) = render a <> " => " <> render b
  render ZSymbol = "Symbol"
  render p@(ZPair l r) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (ZValue x) = "{" <> render (project x :: Untyped') <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"
  render ZAny = "Any"

newtype Native = Native (Typed' -> Either (NativeException ()) Typed')

instance Eq Native where
  _ == _ = bug EqUndefined

instance Show Native where
  show _ = "Native <native>"

newtype Native' = Native' (forall l. (Location l) => Typed l -> Either (NativeException l) (Typed l))

instance Eq Native' where
  _ == _ = bug EqUndefined

instance Show Native' where
  show _ = "Native' <native>"

newtype NativeIO = NativeIO (IO Typed')

instance Eq NativeIO where
  _ == _ = bug EqUndefined

instance Show NativeIO where
  show _ = "NativeIO <nativeIO>"

instance (Location l) => Magma (l, ZType) where
  (lx, tx) >< (ly, ty) = (lx <> ly, tx >< ty)

instance (Location l) => Magma (Typed l) where
  x@(_ :# lx) >< y@(_ :# ly) = EPair x y :# (lx >< ly)

instance MaybeList Untyped' where
  isList (LocU EUnit) = True
  isList (LocU (EPair _ r)) = isList r
  isList _ = False

  maybeList (LocU EUnit) = Just []
  maybeList (LocU (EPair l r)) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance MaybeList (LocF Expr l) where
  isList (EUnit :# _) = True
  isList (EPair _ r :# _) = isList r
  isList _ = False

  maybeList (EUnit :# _) = Just []
  maybeList (EPair l r :# _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance Render Untyped' where
  render e@(LocU e') = go e'
    where
      go (EType z) = "[" <> render z <> "]"
      go EUnit = "()"
      go (ESymbol t) = render t
      go ELambda1 {} = "<lambda>"
      go ELambdaN {} = "<lambda>"
      go EImplicit {} = "<implicit>"
      go (EMacro1 v x) = "(macro " <> render v <> " " <> render x <> ")"
      go (EMacroN vs x) = "(macro " <> render vs <> " " <> render x <> ")"
      go (EPair l r) =
        case maybeList e of
          Just xs -> render xs
          Nothing -> render (l, r)
      go (EAnnotation x z) = "(" <> render x <> " : " <> render z <> ")"
      go (EApply1 f x) = go (EPair f x)
      go (EApplyN f xs) =
        "(" <> T.intercalate " " (render f : toList (render <$> xs)) <> ")"
      go (EQuote t) = "'" <> render t
      go (ENative _) = "<native>"
      go (ENative' _) = "<native>"
      go (ENativeIO _) = "<nativeIO>"
      go ESpecial = "<special>"

instance (Location l) => Render (Untyped (Maybe l)) where
  render e = render (project e :: Untyped')

instance Render Typed' where
  render e@(_ :# t) = render (project e :: Untyped') <> " : " <> render t

instance Render (Typed l) where
  render e = render (project e :: Typed')

exprType :: Typed l -> ZType
exprType (_ :# (_, t)) = t

exprType' :: Typed' -> ZType
exprType' (_ :# t) = t

unwrapType :: Typed l -> ZType
unwrapType ((EType z) :# _) = z
unwrapType e = ZValue (project e)

unwrapUntyped :: ZType -> Untyped'
unwrapUntyped (ZUntyped e) = e
unwrapUntyped (ZValue e) = bug (UnwrapUntypedTyped e)
unwrapUntyped z = LocU (EType z)

setType :: ZType -> Typed l -> Typed l
setType z (e :# (l, _)) = e :# (l, z)

typeTuple :: [ZType] -> ZType
typeTuple = foldr (><) ZUnit

untypedTuple :: (Location l) => NonEmpty (Untyped l) -> Untyped l
untypedTuple (x@(_ :# lx) :| xs) =
  case nonEmpty xs of
    Nothing -> EPair x (EUnit :# locEnd lx) :# lx
    Just xs' ->
      let y@(_ :# ly) = untypedTuple xs'
       in EPair x y :# (lx <> ly)

typedTuple :: (Location l) => NonEmpty (Typed l) -> Typed l
typedTuple (x@(_ :# (l, _)) :| xs) =
  case nonEmpty xs of
    Nothing -> x >< (EUnit :# (locEnd l, ZUnit))
    Just xs' -> x >< typedTuple xs'
