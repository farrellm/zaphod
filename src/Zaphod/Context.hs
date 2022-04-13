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

import Lens.Micro.Platform (use, (<~))
import Relude.Extra.Map ((!?))
import Zaphod.Types

data ContextBug
  = MissingMarkerInContext Existential
  | MissingUniversalInContext Universal
  | MissingVarInContext Variable
  | MissingExistentialInContext Existential
  | UnexpectedExistentialInSolve Existential Existential
  | NotMonotype (ZType Typed')
  deriving (Show)

instance Exception ContextBug

wind :: Existential -> Context l -> (Hole l, Context l)
wind e (Context cs) =
  let (l, r) = go cs []
   in (Hole e r, Context l)
  where
    go [] _ = bug $ MissingExistentialInContext e
    go (CUnsolved f : ds) rs | e == f = (ds, rs)
    go (d : ds) rs = go ds (d : rs)

unwind :: Hole l -> Context l -> Context l
unwind (Hole e rs) (Context es) = Context (flipfoldl' (:) (CUnsolved e : es) rs)

lookupType :: Existential -> Context l -> LookupResult l
lookupType t (Context es) = go es
  where
    go [] = RMissing
    go (CUnsolved k : _)
      | k == t = RUnsolved
    go (CSolved k v : _)
      | k == t = RSolved v
    go (_ : rs) = go rs

lookupVar :: Variable -> Context l -> Maybe (ZType (Typed l))
lookupVar t (Context es) = go es
  where
    go [] = Nothing
    go (CVariable k v : _)
      | k == t = Just v
    go (CEnvironment env : rs) = case env !? getVariable t of
      Just v -> Just $ exprType v
      Nothing -> go rs
    go (_ : rs) = go rs

(<:) :: ContextEntry l -> Context l -> Context l
e <: Context cs = Context (e : cs)

dropMarker :: Existential -> Context l -> Context l
dropMarker a (Context es) = Context $ go es
  where
    go (CMarker b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingMarkerInContext a

dropUniversal :: Universal -> Context l -> Context l
dropUniversal a (Context es) = Context $ go es
  where
    go (CUniversal b : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingUniversalInContext a

dropVar :: Variable -> Context l -> Context l
dropVar a (Context es) = Context $ go es
  where
    go (CVariable b _ : rs) | a == b = rs
    go (_ : rs) = go rs
    go [] = bug $ MissingVarInContext a

substitute :: forall l. ZType (Typed l) -> ZType (Typed l) -> ZType (Typed l) -> ZType (Typed l)
substitute x y z | z == y = x
substitute x y (ZForall beta b) = ZForall beta (substitute x y b)
substitute x y (ZFunction a b) = ZFunction (substitute x y a) (substitute x y b)
substitute x y (ZImplicit a b) = ZImplicit (substitute x y a) (substitute x y b)
substitute x y (ZPair a b) = ZPair (substitute x y a) (substitute x y b)
substitute x y (ZValue e) = ZValue (substituteValue e)
  where
    substituteValue :: Typed l -> Typed l
    substituteValue z@(EUnit :@ _) = z
    substituteValue (ESymbol s :@ (l, t)) =
      ESymbol s :@ (l, substitute x y t)
    substituteValue ((EPair a b) :@ (l, t)) =
      EPair (substituteValue a) (substituteValue b) :@ (l, substitute x y t)
    substituteValue ((EType z) :@ (l, t)) =
      EType (substitute x y z) :@ (l, substitute x y t)
    substituteValue z = bug (NotImplemented $ render z)
substitute _ _ z@ZUnit = z
substitute _ _ z@ZSymbol = z
substitute _ _ z@ZAny = z
substitute _ _ z@ZAnyType = z
substitute _ _ z@(ZType _) = z
substitute _ _ z@(ZUniversal _) = z
substitute _ _ z@(ZExistential _) = z

solveExistential ::
  (MonadState (CheckerState l) m, MonadError (CheckerException l) m) =>
  ZType (Typed l) ->
  Existential ->
  m ()
solveExistential z e = do
  (Context cs) <- use context
  context <~ Context <$> go cs
  where
    go (CUnsolved f : rs) | e == f = pure $ CSolved f z : rs
    go (CSolved f y : _)
      | e == f = throwError $ ExistentialAlreadySolved (project z) f (project y)
    go (CSolved f q : rs) =
      (CSolved f ((z `substitute` ZExistential e) q) :) <$> go rs
    go (CVariable x q : rs) =
      (CVariable x ((z `substitute` ZExistential e) q) :) <$> go rs
    go (r : rs) = (r :) <$> go rs
    go [] = bug $ MissingExistentialInContext e

isWellFormed :: ZType (Typed l) -> Context l -> Bool
isWellFormed (ZType _) _ = True
isWellFormed ZAny _ = True
isWellFormed ZAnyType _ = True
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
isWellFormed z@(ZForall _ _) _ = bug (NotMonotype $ project z)
isWellFormed (ZValue x) ctx = isWellFormed (exprType x) ctx
isWellFormed _ (Context []) = False
