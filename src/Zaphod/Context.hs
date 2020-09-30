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

import qualified Data.Map as M
import Zaphod.Types

data ContextBug
  = MissingMarkerInContext Existential
  | MissingUniversalInContext Universal
  | MissingVarInContext Variable
  | MissingExistentialInContext Existential
  | ExistentialAlreadySolved ZType Existential
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
    go (CEnvironment env : rs) = case M.lookup (getVariable t) env of
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
substitute x y (ZPair a b) = ZPair (substitute x y a) (substitute x y b)
substitute _ _ z = z

solveExistential :: ZType -> Existential -> Context -> Context
solveExistential z e (Context cs) = Context $ go cs
  where
    go (CUnsolved f : rs) | e == f = CSolved f z : rs
    go (CSolved f _y : _) | e == f = bug $ ExistentialAlreadySolved z e
    go (CSolved f q : rs) = CSolved f ((z `substitute` ZExistential e) q) : go rs
    go (CVariable x q : rs) = CVariable x ((z `substitute` ZExistential e) q) : go rs
    go (r : rs) = r : go rs
    go [] = bug $ MissingExistentialInContext e

isWellFormed :: ZType -> Context -> Bool
isWellFormed ZAny _ = True
isWellFormed ZUnit _ = True
isWellFormed ZSymbol _ = True
isWellFormed (ZFunction a b) ctx = isWellFormed a ctx && isWellFormed b ctx
isWellFormed (ZPair a b) ctx = isWellFormed a ctx && isWellFormed b ctx
isWellFormed (ZType _) _ = True
isWellFormed (ZUniversal a) (Context (CUniversal b : _)) | a == b = True
isWellFormed (ZExistential a) (Context (CUnsolved b : _)) | a == b = True
isWellFormed (ZExistential a) (Context (CSolved b _ : _)) | a == b = True
isWellFormed z@(ZUniversal _) (Context (_ : rs)) = isWellFormed z (Context rs)
isWellFormed z@(ZExistential _) (Context (_ : rs)) = isWellFormed z (Context rs)
isWellFormed z@(ZForall _ _) _ = bug (NotMonotype z)
isWellFormed (ZValue x) ctx = isWellFormed (exprType x) ctx
isWellFormed (ZUntyped x) _ = bug (WellFormedUntyped x)
isWellFormed _ (Context []) = False
