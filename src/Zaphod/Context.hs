{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod.Context
  ( wind,
    unwind,
    lookupType,
    lookupVar,
    (<:),
    dropMarker,
    dropUniversal,
    dropVar,
    substitute,
    solveExistential,
    isWellFormed,
  )
where

import Lens.Micro.Mtl (use, (<~))
import Relude.Extra.Map ((!?))
import Zaphod.Types

data ContextBug
  = MissingMarkerInContext Existential
  | MissingUniversalInContext Universal
  | MissingVarInContext Variable
  | MissingExistentialInContext Existential
  | UnexpectedExistentialInSolve Existential Existential
  | NotMonotype ZType
  | WellFormedUntyped (Untyped ())
  deriving (Show)

instance Exception ContextBug

wind :: Existential -> Context -> (Hole, Context)
wind e (Context cs) =
  let (l, r) = go cs []
   in (Hole e r, Context l)
  where
    go [] _ = bug $ MissingExistentialInContext e
    go (CUnsolved f : ds) rs | e == f = (ds, rs)
    go (d : ds) rs = go ds (d : rs)

unwind :: Hole -> Context -> Context
unwind (Hole e rs) (Context es) = Context (flipfoldl' (:) (CUnsolved e : es) rs)

lookupType :: Existential -> Context -> LookupResult
lookupType t (Context es) = go es
  where
    go [] = RMissing
    go (CUnsolved k : _)
      | k == t = RUnsolved
    go (CSolved k v : _)
      | k == t = RSolved v
    go (_ : rs) = go rs

lookupVar :: Variable -> Context -> Maybe ZType
lookupVar t (Context es) = go es
  where
    go [] = Nothing
    go (CVariable k v : _)
      | k == t = Just v
    go (CEnvironment env : rs) = case env !? getVariable t of
      Just v -> Just $ exprType v
      Nothing -> go rs
    go (_ : rs) = go rs

(<:) :: ContextEntry -> Context -> Context
e <: Context cs = Context (e : cs)

dropMarker :: Existential -> Context -> Context
dropMarker a (Context es) = Context $ go es
  where
    go (CMarker b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingMarkerInContext a

dropUniversal :: Universal -> Context -> Context
dropUniversal a (Context es) = Context $ go es
  where
    go (CUniversal b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingUniversalInContext a

dropVar :: Variable -> Context -> Context
dropVar a (Context es) = Context $ go es
  where
    go (CVariable b _ : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingVarInContext a

substitute :: ZType -> ZType -> ZType -> ZType
substitute x y z | z == y = x
substitute x y (ZForall beta b) = ZForall beta (substitute x y b)
substitute x y (ZFunction a b) = ZFunction (substitute x y a) (substitute x y b)
substitute x y (ZImplicit a b) = ZImplicit (substitute x y a) (substitute x y b)
substitute x y (ZPair a b) = ZPair (substitute x y a) (substitute x y b)
substitute x y (ZValue e) = ZValue (substituteValue x y e)
substitute _ _ t@(ZUntyped _) = bug (NotImplemented $ render t)
substitute _ _ z@ZUnit = z
substitute _ _ z@ZSymbol = z
substitute _ _ z@ZAny = z
substitute _ _ z@(ZType _) = z
substitute _ _ z@(ZUniversal _) = z
substitute _ _ z@(ZExistential _) = z

substituteValue :: ZType -> ZType -> Typed l -> Typed l
substituteValue _ _ e@(EUnit :@ _) = e
substituteValue x y (ESymbol s t :@ l) = ESymbol s (substitute x y t) :@ l
substituteValue x y (EPair l r t :@ o) =
  EPair
    (substituteValue x y l)
    (substituteValue x y r)
    (substitute x y t)
    :@ o
substituteValue _ _ e = bug (NotImplemented $ render (stripLocation e))

solveExistential ::
  (MonadState CheckerState m, MonadError (CheckerException l) m, Monoid l) =>
  ZType ->
  Existential ->
  m ()
solveExistential z e = do
  (Context cs) <- use context
  context <~ Context <$> go cs
  where
    go (CUnsolved f : rs) | e == f = pure $ CSolved f z : rs
    go (CSolved f y : _)
      | e == f = throwError $ ExistentialAlreadySolved z f y
    go (CSolved f q : rs) =
      (CSolved f ((z `substitute` ZExistential e) q) :) <$> go rs
    go (CVariable x q : rs) =
      (CVariable x ((z `substitute` ZExistential e) q) :) <$> go rs
    go (r : rs) = (r :) <$> go rs
    go [] = bug $ MissingExistentialInContext e

isWellFormed :: ZType -> Context -> Bool
isWellFormed (ZType _) _ = True
isWellFormed ZAny _ = True
isWellFormed ZUnit _ = True
isWellFormed ZSymbol _ = True
isWellFormed (ZFunction a b) ctx = isWellFormed a ctx && isWellFormed b ctx
isWellFormed (ZImplicit a b) ctx = isWellFormed a ctx && isWellFormed b ctx
isWellFormed (ZPair a b) ctx = isWellFormed a ctx && isWellFormed b ctx
isWellFormed (ZUniversal a) (Context (CUniversal b : _)) | a == b = True
isWellFormed (ZExistential a) (Context (CUnsolved b : _)) | a == b = True
isWellFormed (ZExistential a) (Context (CSolved b _ : _)) | a == b = True
isWellFormed z@(ZUniversal _) (Context (_ : rs)) = isWellFormed z (Context rs)
isWellFormed z@(ZExistential _) (Context (_ : rs)) = isWellFormed z (Context rs)
isWellFormed z@(ZForall _ _) _ = bug (NotMonotype z)
isWellFormed (ZValue x) ctx = isWellFormed (exprType x) ctx
isWellFormed (ZUntyped x) _ = bug (WellFormedUntyped $ stripLocation x)
isWellFormed _ (Context []) = False
