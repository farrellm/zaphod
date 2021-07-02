{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod.Types.Expr where

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.MonoTraversable
import qualified GHC.Exts as GE
import qualified GHC.Show (Show (..))
import Relude.Extra.Map
import Zaphod.Types.Class
import Zaphod.Types.Location
import Zaphod.Types.Wrapper

deriving instance (Show t) => Show (LocU Expr t)

deriving instance (Show t, Show l) => Show (LocB Expr t l)

deriving instance (Eq t) => Eq (LocU Expr t)

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
  = TypeMismatch Text (Typed ()) l Text
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

data Expr t f
  = EType ZType
  | EUnit
  | ESymbol Symbol t
  | ELambda1 Variable f (Environment f) t
  | ELambdaN [Variable] f (Environment f) t
  | EImplicit Variable f (Environment f) t
  | EMacro1 Variable f t
  | EMacroN [Variable] f t
  | EApply1 f f t
  | EApplyN f (NonEmpty f) t
  | EPair f f t
  | EAnnotation f ZType
  | EQuote f t
  | ENative Native t
  | ENative' Native' t
  | ENativeIO NativeIO t
  | ESpecial t
  deriving (Show, Eq, Functor, Foldable, Traversable)

type family Untyped l where
  Untyped () = LocU Expr ()
  Untyped l = LocB Expr () l

type family Typed l where
  Typed () = LocU Expr ZType
  Typed l = LocB Expr ZType l

class
  (HasLocation a, Value a ~ Expr t a, Locat a ~ l) =>
  LocationExpr a t l
    | a -> t l
  where
  stripLocation :: a -> LocU Expr t
  setLocation :: l -> LocU Expr t -> a
  expr :: a -> Expr t a
  expr = value
  {-# INLINE expr #-}

pattern (:@@) :: (HasLocation a) => Value a -> Locat a -> a
pattern (:@@) x l <-
  (splitLocation -> (x, l))
  where
    x :@@ l = withLocation x l

{-# COMPLETE (:@@) :: Untyped #-}

{-# COMPLETE (:@@) :: Typed #-}

instance Location l => LocationExpr (LocB Expr t l) t l where
  stripLocation = bToU . void
    where
      bToU (v :@ ()) = LocU $ fmap bToU v
  setLocation l = uToB
    where
      uToB (LocU v) = fmap uToB v :@ l

instance LocationExpr (LocU Expr t) t () where
  stripLocation x = x
  {-# INLINE stripLocation #-}
  setLocation () x = x
  {-# INLINE setLocation #-}

type CUntyped l =
  ( LocationExpr (Untyped l) () l,
    Render (Untyped l),
    Magma (Untyped l),
    Eq (Untyped ())
  )

type CTyped l =
  ( LocationExpr (Typed l) ZType l,
    Render (Typed l),
    MaybeList (Typed l),
    Magma (Typed l),
    Eq (Typed ()),
    MonoFunctor (Typed l),
    MonoTraversable (Typed l),
    Element (Typed l) ~ ZType
  )

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

instance Magma ZType where
  (><) = ZPair
  tuple = foldr (><) ZUnit

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
  render (ZValue x) = "{" <> render (void x) <> "}"
  render (ZUntyped x) = "{" <> render x <> "}"
  render ZAny = "Any"

newtype Native = Native (Typed () -> Either (NativeException ()) (Typed ()))

instance Eq Native where
  _ == _ = bug EqUndefined

instance Show Native where
  show _ = "Native <native>"

newtype Native' = Native' (forall l. (CTyped l) => Typed l -> Either (NativeException l) (Typed l))

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

instance Magma (LocU Expr ()) where
  x >< y = LocU (EPair x y ())
  tuple (x :| xs) =
    case nonEmpty xs of
      Nothing -> LocU $ EPair x (LocU EUnit) ()
      Just xs' -> LocU $ EPair x (tuple xs') ()

instance Magma (LocU Expr ZType) where
  x >< y = LocU (EPair x y (exprType x >< exprType y))
  tuple (x :| xs) =
    case nonEmpty xs of
      Nothing -> LocU $ EPair x (LocU EUnit) (exprType x >< ZUnit)
      Just xs' ->
        let xs'' = tuple xs'
         in LocU $ EPair x xs'' (exprType x >< exprType xs'')

instance MaybeList (LocU Expr t) where
  isList (LocU EUnit) = True
  isList (LocU (EPair _ r _)) = isList r
  isList _ = False

  maybeList (LocU EUnit) = Just []
  maybeList (LocU (EPair l r _)) = (l :) <$> maybeList r
  maybeList _ = Nothing

type instance Element (LocU Expr t) = t

instance MonoFunctor (LocU Expr t)

instance MonoFoldable (LocU Expr t)

instance MonoTraversable (LocU Expr t)

type instance Element (LocB Expr t l) = t

instance MonoFunctor (LocB Expr t l) where
  omap = first

instance MonoFoldable (LocB Expr t l) where
  ofoldl1Ex' = undefined
  ofoldr1Ex = undefined
  ofoldl' f = bifoldl' f const
  ofoldr f = bifoldr f (const id)
  ofoldMap f = bifoldMap f (const mempty)

instance MonoTraversable (LocB Expr t l) where
  otraverse f = bitraverse f pure

instance (Location l) => Magma (LocB Expr () l) where
  x@(_ :@ lx) >< y@(_ :@ ly) = EPair x y () :@ (lx <> ly)
  tuple (x@(_ :@ lx) :| xs) =
    case nonEmpty xs of
      Nothing -> EPair x (EUnit :@ locEnd lx) () :@ lx
      Just xs' ->
        let xs'' = tuple xs'
         in EPair x xs'' () :@ (lx <> location xs'')

instance (Location l) => Magma (LocB Expr ZType l) where
  x@(_ :@ lx) >< y@(_ :@ ly) = EPair x y (ZPair (exprType x) (exprType y)) :@ (lx <> ly)
  tuple (x@(_ :@ lx) :| xs) =
    case nonEmpty xs of
      Nothing -> EPair x (EUnit :@ locEnd lx) (ZPair (exprType x) ZUnit) :@ lx
      Just xs' ->
        let xs'' = tuple xs'
         in EPair x xs'' (ZPair (exprType x) (exprType xs'')) :@ (lx <> location xs'')

instance MaybeList (LocB Expr l t) where
  isList (EUnit :@ _) = True
  isList (EPair _ r _ :@ _) = isList r
  isList _ = False

  maybeList (EUnit :@ _) = Just []
  maybeList (EPair l r _ :@ _) = (l :) <$> maybeList r
  maybeList _ = Nothing

instance Render (LocU Expr ()) where
  render (LocU (EType z)) = "[" <> render z <> "]"
  render (LocU EUnit) = "()"
  render (LocU (ESymbol t ())) = render t
  render (LocU (ELambda1 _ _ _ ())) = "<lambda>"
  render (LocU (ELambdaN _ _ _ ())) = "<lambda>"
  render (LocU (EImplicit _ _ _ ())) = "<implicit>"
  render (LocU (EMacro1 x e ())) = "(macro " <> render x <> " " <> render e <> ")"
  render (LocU (EMacroN xs e ())) = "(macro " <> render xs <> " " <> render e <> ")"
  render p@(LocU (EPair l r ())) =
    case maybeList p of
      Just xs -> render xs
      Nothing -> render (l, r)
  render (LocU (EAnnotation e z)) = "(" <> render e <> " : " <> render z <> ")"
  render (LocU (EApply1 f x ())) = render (LocU $ EPair f x ())
  render (LocU (EApplyN f xs ())) =
    let xs' = tuple xs
     in render (LocU $ EPair f xs' ())
  render (LocU (EQuote t ())) = "'" <> render t
  render (LocU (ENative _ ())) = "<native>"
  render (LocU (ENative' _ ())) = "<native>"
  render (LocU (ENativeIO _ ())) = "<nativeIO>"
  render (LocU (ESpecial ())) = "<special>"

instance Render (LocU Expr ZType) where
  render e = render (void e) <> " : " <> render (exprType e)

instance (Render (LocU Expr z), Location l) => Render (LocB Expr z l) where
  render = render . stripLocation

exprType :: (LocationExpr h ZType l) => h -> ZType
exprType = go . expr
  where
    go (EType (ZType n)) = ZType (n + 1)
    go (EType _) = ZType 0
    go EUnit = ZUnit
    go (ELambda1 _ _ _ t) = t
    go (ELambdaN _ _ _ t) = t
    go (EImplicit _ _ _ t) = t
    go (EMacro1 _ _ t) = t
    go (EMacroN _ _ t) = t
    go (EAnnotation _ t) = t
    go (ESymbol _ t) = t
    go (EPair _ _ t) = t
    go (EApply1 _ _ t) = t
    go (EApplyN _ _ t) = t
    go (EQuote _ t) = t
    go (ENative _ t) = t
    go (ENative' _ t) = t
    go (ENativeIO _ t) = t
    go (ESpecial t) = t

unwrapType :: Typed () -> ZType
unwrapType (LocU (EType z)) = z
unwrapType e = ZValue e

unwrapTypes :: NonEmpty (Typed ()) -> ZType
unwrapTypes (y :| []) = ZPair (unwrapType y) ZUnit
unwrapTypes (y :| (z : zs)) = ZPair (unwrapType y) $ unwrapTypes (z :| zs)

unwrapUntyped :: ZType -> Untyped ()
unwrapUntyped (ZUntyped e) = e
unwrapUntyped (ZValue e) = void e
unwrapUntyped z = LocU $ EType z

setType :: (CTyped l) => ZType -> Typed l -> Typed l
setType z h = go (value h) :@@ location h
  where
    go EUnit = EUnit
    go t@(EType _) = t
    go (ESymbol s _) = ESymbol s z
    go (ELambda1 x e env _) = ELambda1 x e env z
    go (ELambdaN xs e env _) = ELambdaN xs e env z
    go (EImplicit x e env _) = EImplicit x e env z
    go (EMacro1 x e _) = EMacro1 x e z
    go (EMacroN xs e _) = EMacroN xs e z
    go (EApply1 f x _) = EApply1 f x z
    go (EApplyN f xs _) = EApplyN f xs z
    go (EPair x y _) = EPair x y z
    go (EAnnotation e _) = EAnnotation e z
    go (EQuote q _) = EQuote q z
    go (ENative n _) = ENative n z
    go (ENative' n _) = ENative' n z
    go (ENativeIO n _) = ENativeIO n z
    go (ESpecial _) = ESpecial z

typeTuple :: [ZType] -> ZType
typeTuple = foldr (><) ZUnit
