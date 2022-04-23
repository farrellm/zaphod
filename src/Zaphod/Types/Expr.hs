{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Expr where

import qualified Data.Text as T
import qualified GHC.Exts as GE
import qualified GHC.Show (Show (..))
import Lens.Micro.Internal (At (..), Index, IxValue, Ixed (..))
import Lens.Micro.Platform ()
import Relude.Extra.Map (DynamicMap (..), StaticMap (..))
import Zaphod.Types.Class (Location (..), Magma (..), MaybeList (..), Projection (project), Render (..))
import Zaphod.Types.Location (LocA (..), LocB (..), LocF (..), LocU (..))
import Zaphod.Types.Wrapper (Existential, Symbol, Universal, Variable)

deriving instance Show (LocU Expr)

deriving instance Eq (LocU Expr)

deriving instance (Show l) => Show (LocF Expr l)

instance Eq (LocF Expr l) where
  (a :# _) == (b :# _) = a == b

deriving instance Show (LocA Expr ZType)

deriving instance Eq (LocA Expr ZType)

deriving instance (Show l) => Show (LocB Expr ZType l)

instance Eq (LocB Expr ZType l) where
  (a :@ _) == (b :@ _) = a == b

data ExprBug
  = EqUndefined
  | MonoidUndefined Text Text
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

type instance Index (Environment e) = Symbol

type instance IxValue (Environment e) = e

instance Ixed (Environment e) where
  ix k f (Environment m) = Environment <$> ix k f m

instance At (Environment e) where
  at k f (Environment m) = Environment <$> at k f m

data Expr f
  = EType (ZType f)
  | EUnit
  | ESymbol Symbol
  | ELambda1 Variable f (Environment f)
  | ELambdaN [Variable] f (Environment f)
  | EImplicit Variable f
  | EMacro1 Variable f (Environment f)
  | EMacroN [Variable] f (Environment f)
  | EApply1 f f
  | EApplyN f [f]
  | EPair f f
  | EAnnotation f (ZType f)
  | EQuote f
  | ENative Native
  | ENative' Native'
  | ENativeIO NativeIO
  | ESpecial
  | EQuasiQuote f
  | EUnquote f
  | EUnquoteSplicing f
  deriving (Show, Eq, Functor, Foldable, Traversable)

type Untyped l = LocF Expr l

type Typed l = LocB Expr ZType l

type Untyped' = LocU Expr

type Typed' = LocA Expr ZType

data ZType f
  = ZType Int
  | ZUnit
  | ZUniversal Universal
  | ZExistential Existential
  | ZForall Universal (ZType f)
  | ZFunction (ZType f) (ZType f)
  | ZImplicit (ZType f) (ZType f)
  | ZSymbol
  | ZPair (ZType f) (ZType f)
  | ZValue f
  | ZAny
  | ZAnyType
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Magma (ZType f) where
  (><) = ZPair

instance MaybeList (ZType f) where
  isList ZUnit = True
  isList (ZPair _ r) = isList r
  isList _ = False

  maybeList ZUnit = Just []
  maybeList (ZPair l r) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance Render (ZType Untyped') where
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
  render (ZValue x) = render x
  render ZAny = "Any"
  render ZAnyType = "AnyType"

instance Render (ZType (Untyped l)) where
  render t = render (project t :: ZType Untyped')

instance Render (ZType Typed') where
  render t = render (project t :: ZType Untyped')

instance Render (ZType (Typed l)) where
  render t = render (project t :: ZType Untyped')

newtype Native = Native (Typed' -> Either (NativeException ()) Typed')

instance Eq Native where
  _ == _ = bug EqUndefined

instance Show Native where
  show _ = "Native <native>"

newtype Native' = Native' (forall l. (Location l) => Typed l -> Either (NativeException ()) (Typed l))

instance Eq Native' where
  _ == _ = bug EqUndefined

instance Show Native' where
  show _ = "Native' <native>"

newtype NativeIO = NativeIO (IO Typed')

instance Eq NativeIO where
  _ == _ = bug EqUndefined

instance Show NativeIO where
  show _ = "NativeIO <nativeIO>"

instance (Location l) => Magma (l, ZType f) where
  (lx, tx) >< (ly, ty) = (lx <> ly, tx >< ty)

instance (Location l) => Magma (Untyped l) where
  x@(_ :# lx) >< y@(_ :# ly) = EPair x y :# (lx <> ly)

instance (Location l) => Magma (Typed l) where
  x@(_ :@ tx) >< y@(_ :@ ty) = EPair x y :@ (tx >< ty)

instance MaybeList Untyped' where
  isList (LocU EUnit) = True
  isList (LocU (EPair _ r)) = isList r
  isList _ = False

  maybeList (LocU EUnit) = Just []
  maybeList (LocU (EPair l r)) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance MaybeList (Typed l) where
  isList (EUnit :@ _) = True
  isList (EPair _ r :@ _) = isList r
  isList _ = False

  maybeList (EUnit :@ _) = Just []
  maybeList (EPair l r :@ _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance Semigroup (ZType (Typed l)) where
  ZUnit <> e = e
  e <> ZUnit = e
  ZPair a b <> e = ZPair a (b <> e)
  a <> b = bug (MonoidUndefined (render a) (render b))

instance (Semigroup l) => Semigroup (Untyped l) where
  EUnit :# _ <> e = e
  e <> EUnit :# _ = e
  EPair a b :# l1 <> e@(_ :# l2) = EPair a (b <> e) :# (l1 <> l2)
  a <> b = bug (MonoidUndefined (render a) (render b))

instance (Semigroup l) => Semigroup (Typed l) where
  EUnit :@ _ <> e = e
  e <> EUnit :@ _ = e
  EPair a b :@ l1 <> e@(_ :@ l2) = EPair a (b <> e) :@ (l1 <> l2)
  a <> b = bug (MonoidUndefined (render a) (render b))

instance Render Untyped' where
  render e@(LocU e') = go e'
    where
      go (EType z) = render z
      go EUnit = "()"
      go (ESymbol t) = render t
      go (ELambda1 v x _) = "(\\" <> render v <> " " <> render x <> ")"
      go (ELambdaN v x _) = "(\\" <> render v <> " " <> render x <> ")"
      go (EImplicit v x) = "(implicit " <> render v <> " " <> render x <> ")"
      go (EMacro1 v x _) = "(macro " <> render v <> " " <> render x <> ")"
      go (EMacroN vs x _) = "(macro " <> render vs <> " " <> render x <> ")"
      go (EPair l r) =
        case maybeList e of
          Just xs -> render xs
          Nothing -> render (l, r)
      go (EAnnotation x z) = "(" <> render x <> " : " <> render z <> ")"
      go (EApply1 f x) = go (EPair f x)
      go (EApplyN f xs) =
        "(" <> T.intercalate " " (render f : toList (render <$> xs)) <> ")"
      go (EQuote t) = "'" <> render t
      go (EQuasiQuote t) = "`" <> render t
      go (EUnquote t) = "," <> render t
      go (EUnquoteSplicing t) = ",@" <> render t
      go (ENative _) = "<native>"
      go (ENative' _) = "<native>"
      go (ENativeIO _) = "<nativeIO>"
      go ESpecial = "<special>"

instance Render (Untyped l) where
  render e = render (project e :: Untyped')

instance Render Typed' where
  render e@(_ :$ t) = render (project e :: Untyped') <> " : " <> render t

instance Render (Typed l) where
  render e = render (project e :: Typed')

exprType :: Typed l -> ZType (Typed l)
exprType (_ :@ (_, t)) = t

setType :: ZType (Typed l) -> Typed l -> Typed l
setType z (e :@ (l, _)) = e :@ (l, z)

typeTuple :: [ZType l] -> ZType l
typeTuple = foldr (><) ZUnit

untypedTuple :: (Location l, Monoid l) => [Untyped l] -> Untyped l
untypedTuple [] = EUnit :# mempty
untypedTuple [x@(_ :# lx)] = EPair x (EUnit :# locEnd lx) :# lx
untypedTuple (x : xs) = x >< untypedTuple xs

typedTuple :: (Location l, Monoid l) => [Typed l] -> Typed l
typedTuple [] = EUnit :@ (mempty, ZUnit)
typedTuple [x@(_ :@ (l, _))] = x >< (EUnit :@ (locEnd l, ZUnit))
typedTuple (x : xs) = x >< typedTuple xs
