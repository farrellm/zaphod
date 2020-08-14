{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod.Context where

import Zaphod.Types

data ContextBug
  = MissingMarkerInContext Existential Context
  | MissingUniversalInContext Universal Context
  | MissingVarInContext Variable Context
  | MissingExistentialInContext Existential Context
  | ExistentialAlreadySolved Existential Context
  | UnexpectedExistentialInSolve Existential Existential
  deriving (Show)

instance Exception ContextBug

wind :: Existential -> Context -> (Hole, Context)
wind e ctx@(Context cs) =
  let (l, r) = go cs []
   in (Hole e r, Context l)
  where
    go [] _ = bug $ MissingExistentialInContext e ctx
    go (CUnsolved f : ds) rs | e == f = (ds, rs)
    go (d : ds) rs = go ds (d : rs)

unwind :: Hole -> Context -> Context
unwind (Hole e rs) (Context es) = Context (foldl' (flip (:)) (CUnsolved e : es) rs)

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
    go (_ : rs) = go rs

(<:) :: ContextEntry -> Context -> Context
e <: Context cs = Context (e : cs)

dropMarker :: Existential -> Context -> Context
dropMarker a ctx@(Context es) = Context $ go es
  where
    go (CMarker b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingMarkerInContext a ctx

dropUniversal :: Universal -> Context -> Context
dropUniversal a ctx@(Context es) = Context $ go es
  where
    go (CUniversal b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingUniversalInContext a ctx

dropVar :: Variable -> Context -> Context
dropVar a ctx@(Context es) = Context $ go es
  where
    go (CVariable b _ : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingVarInContext a ctx

substitute :: ZType -> ZType -> ZType -> ZType
substitute x y z | z == y = x
substitute x y (ZForall beta b) = ZForall beta (substitute x y b)
substitute x y (ZFunction a b) = ZFunction (substitute x y a) (substitute x y b)
substitute x y (ZPair a b) = ZPair (substitute x y a) (substitute x y b)
substitute _ _ z = z

solveExistential :: ZType -> Existential -> Context -> Context
solveExistential z e ctx@(Context cs) = Context $ go cs
  where
    go (CUnsolved f : rs) | e == f = CSolved f z : rs
    go (CSolved f _ : _) | e == f = bug $ ExistentialAlreadySolved e ctx
    go (CSolved f q : rs) = CSolved f ((z `substitute` ZExistential e) q) : go rs
    go (CVariable x q : rs) = CVariable x ((z `substitute` ZExistential e) q) : go rs
    go (r : rs) = r : go rs
    go [] = bug $ MissingExistentialInContext e ctx
