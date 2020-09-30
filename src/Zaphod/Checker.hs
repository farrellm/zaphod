{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Checker (check, synthesize) where

import qualified Data.Text as T
import Lens.Micro.Mtl
import Zaphod.Context
import Zaphod.Types

data ZaphodError
  = UndefinedVariable Variable
  | TypeError Text
  deriving (Show)

instance Exception ZaphodError

data ZaphodBug
  = CannotApply ZType (Untyped ())
  | NotMonotype ZType
  | NotQuotable (Untyped ())
  | UnexpectedUntyped (Untyped ())
  | UnexpectedTyped (Typed ())
  | LambdaMissmatch [Variable] ZType
  | Native
  | Special
  | NotList (Typed ())
  | Impossible
  deriving (Show)

instance Exception ZaphodBug

bind2 :: (Monad m) => (a -> b -> m c) -> m a -> m b -> m c
bind2 f x y = do
  x' <- x
  y' <- y
  f x' y'

nextExtential :: (MonadState CheckerState m) => m Existential
nextExtential = do
  c <- existentialData <<%= succ
  let n = Existential $ fromString [c]
  context %= (CUnsolved n <:)
  pure n

markExtential :: (MonadState CheckerState m) => (Existential -> m a) -> m a
markExtential x = do
  c <- existentialData <<%= succ
  let n = Existential $ fromString [c]
  context %= (CMarker n <:)
  context %= (CUnsolved n <:)
  res <- x n
  context %= dropMarker n
  pure res

withHole :: (MonadState CheckerState m) => Existential -> m a -> m a
withHole e x = do
  (h, ctx) <- wind e <$> use context
  context .= ctx
  res <- x
  context %= unwind h
  pure res

withUniversal :: (MonadState CheckerState m) => Universal -> m a -> m a
withUniversal alpha x = do
  context %= (CUniversal alpha <:)
  res <- x
  context %= dropUniversal alpha
  pure res

applyCtxType :: (MonadState CheckerState m) => ZType -> m ZType
applyCtxType z@(ZType _) = pure z
applyCtxType ZTop = pure ZTop
applyCtxType z@(ZUniversal _) = pure z
applyCtxType ZUnit = pure ZUnit
applyCtxType ZSymbol = pure ZSymbol
applyCtxType z@(ZExistential x) = do
  ctx <- use context
  case lookupType x ctx of
    RSolved t -> pure t
    _ -> pure z
applyCtxType (ZFunction a b) = ZFunction <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZPair a b) = ZPair <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZForall a t) = ZForall a <$> applyCtxType t
applyCtxType (ZValue x) = ZValue <$> applyCtxExpr x
applyCtxType (ZUntyped x) = bug (UnexpectedUntyped x)

applyCtxExpr :: (MonadState CheckerState m) => Typed l -> m (Typed l)
applyCtxExpr (EType t :@ l) = (:@ l) . EType <$> applyCtxType t
applyCtxExpr (EAnnotation e t :@ l) = (:@ l) <$> (EAnnotation <$> applyCtxExpr e <*> applyCtxType t)
applyCtxExpr e = bitraverse applyCtxType pure e

notInFV :: Existential -> ZType -> Bool
notInFV _ (ZType _) = True
notInFV _ ZTop = True
notInFV _ ZUnit = True
notInFV _ (ZUniversal _) = True
notInFV a (ZExistential b) = a /= b
notInFV a (ZForall _ b) = notInFV a b
notInFV a (ZFunction b c) = notInFV a b && notInFV a c
notInFV a (ZPair b c) = notInFV a b && notInFV a c
notInFV _ ZSymbol = True
notInFV a (ZValue x) = notInFV a (exprType x)
notInFV _ (ZUntyped x) = bug (UnexpectedUntyped x)

isMonoType :: ZType -> Bool
isMonoType ZTop = True
isMonoType ZUnit = True
isMonoType ZSymbol = True
isMonoType (ZUniversal _) = True
isMonoType (ZExistential _) = True
isMonoType (ZType _) = True
isMonoType (ZFunction a b) = isMonoType a && isMonoType b
isMonoType (ZPair a b) = isMonoType a && isMonoType b
isMonoType (ZValue v) = isMonoTypeValue v
  where
    isMonoTypeValue (ESymbol _ ZSymbol :@ _) = True
    isMonoTypeValue (EPair l r _ :@ _) = isMonoTypeValue l && isMonoTypeValue r
    isMonoTypeValue (EType t :@ _) = isMonoType t
    isMonoTypeValue _ = False
isMonoType _ = False

isDeeper :: (MonadState CheckerState m) => ZType -> Existential -> m Bool
isDeeper tau alphaHat = do
  ctx <- _context <$> get
  let ctx' = dropExistential ctx
  pure (isWellFormed tau ctx')
  where
    dropExistential (Context []) = Context []
    dropExistential (Context (CSolved b _ : rs)) | alphaHat == b = Context rs
    dropExistential (Context (CUnsolved b : rs)) | alphaHat == b = Context rs
    dropExistential (Context (_ : rs)) = dropExistential $ Context rs

subtype :: (MonadState CheckerState m) => ZType -> ZType -> m ()
subtype a b =
  logInfo ("sub " <> render a <> " <: " <> render b) $
    subtype' a b

instantiateL :: (MonadState CheckerState m) => Existential -> ZType -> m ()
instantiateL a b =
  logInfo ("inL " <> render a <> " =: " <> render b) $
    instantiateL' a b

instantiateR :: (MonadState CheckerState m) => ZType -> Existential -> m ()
instantiateR a b =
  logInfo ("inR " <> render a <> " := " <> render b) $
    instantiateR' a b

check :: (Monoid l, MonadState CheckerState m) => Untyped l -> ZType -> m (Typed l)
check a b =
  logInfo ("chk " <> render a <> " =: " <> render b) $
    check' a b

synthesize :: (Monoid l, MonadState CheckerState m) => Untyped l -> m (Typed l)
synthesize a =
  logInfo ("syn " <> render a) $
    synthesize' a

applySynth :: (Monoid l, MonadState CheckerState m) => ZType -> Untyped l -> m (Typed l, ZType)
applySynth a b =
  logInfo ("app " <> render a <> " =>> " <> render b) $
    applySynth' a b

logInfo :: (Render a, MonadState CheckerState m) => Text -> m a -> m a
logInfo m x = do
  i <- mkIndent
  ctx <- use context
  traceM' (i <> "<" <> m)
  traceM' (i <> "|    " <> render ctx)
  depth += 1
  res <- x
  depth -= 1
  ctx' <- use context
  traceM' (i <> ">    " <> render res)
  traceM' (i <> "     " <> render ctx')
  pure res
  where
    mkIndent :: (MonadState CheckerState m) => m Text
    mkIndent = flip T.replicate "| " <$> use depth

subtype' :: (MonadState CheckerState m) => ZType -> ZType -> m ()
-- <:Top
subtype' _ ZTop = pass
-- <:Var
subtype' (ZUniversal alpha) (ZUniversal beta) | alpha == beta = pass
-- <:Unit
subtype' ZUnit ZUnit = pass
-- <:Exvar
subtype' (ZExistential alphaHat) (ZExistential betaHat) | alphaHat == betaHat = pass
-- <:->
subtype' (ZFunction a1 a2) (ZFunction b1 b2) = do
  bind2 subtype (applyCtxType b1) (applyCtxType a1)
  bind2 subtype (applyCtxType a2) (applyCtxType b2)
-- <:Pair
subtype' (ZPair a1 a2) (ZPair b1 b2) = do
  bind2 subtype (applyCtxType a1) (applyCtxType b1)
  bind2 subtype (applyCtxType a2) (applyCtxType b2)
-- <:∀L
subtype' (ZForall alpha a) b =
  markExtential $ \alphaHat ->
    (ZExistential alphaHat `substitute` ZUniversal alpha) a `subtype` b
-- <:∀R
subtype' a (ZForall alpha b) =
  withUniversal alpha $ a `subtype` b
-- <:InstantiateL
subtype' (ZExistential alphaHat) a | alphaHat `notInFV` a = alphaHat `instantiateL` a
-- <:InstantiateR
subtype' a (ZExistential alphaHat) | alphaHat `notInFV` a = a `instantiateR` alphaHat
-- <:Symbol
subtype' ZSymbol ZSymbol = pass
-- <:Type
subtype' (ZType m) (ZType n) | m == n = pass
-- <:Value
subtype' (ZValue (ESymbol a ZSymbol :@ _)) (ZValue (ESymbol b ZSymbol :@ _)) | a == b = pass
--
subtype' a b = bug $ TypeError (render a <> " is not a subtype of " <> render b)

instantiateL' :: (MonadState CheckerState m) => Existential -> ZType -> m ()
instantiateL' alphaHat x = do
  d <-
    if isMonoType x
      then isDeeper x alphaHat
      else pure False
  -- traceShowM d
  go d x
  where
    -- InstLSolve
    go True tau = context %= solveExistential tau alphaHat
    -- InstLReach
    go _ (ZExistential betaHat) =
      context %= solveExistential (ZExistential alphaHat) betaHat
    -- InstLArr
    go _ (ZFunction a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e2 <- nextExtential
          e1 <- nextExtential
          pure (e1, e2)
      context
        %= solveExistential
          (ZFunction (ZExistential alphaHat1) (ZExistential alphaHat2))
          alphaHat
      a1 `instantiateR` alphaHat1
      alphaHat2 `instantiateL` a2
    -- InstLPair
    go _ (ZPair a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      context
        %= solveExistential
          (ZPair (ZExistential alphaHat1) (ZExistential alphaHat2))
          alphaHat
      alphaHat1 `instantiateL` a1
      alphaHat2 `instantiateL` a2
    -- InstLAllR
    go _ (ZForall beta b) = do
      withUniversal beta $ do
        alphaHat `instantiateL` b
    --
    go _ tau = bug $ NotMonotype tau

instantiateR' :: (MonadState CheckerState m) => ZType -> Existential -> m ()
instantiateR' x alphaHat = do
  d <-
    if isMonoType x
      then isDeeper x alphaHat
      else pure False
  -- traceShowM d
  go d x
  where
    -- InstRSolve
    go True tau = context %= solveExistential tau alphaHat
    -- InstRReach
    go _ (ZExistential betaHat) = do
      context %= solveExistential (ZExistential alphaHat) betaHat
    -- InstRArr
    go _ (ZFunction a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      context
        %= solveExistential
          (ZFunction (ZExistential alphaHat1) (ZExistential alphaHat2))
          alphaHat
      (alphaHat1 `instantiateL`) =<< applyCtxType a1
      (`instantiateR` alphaHat2) =<< applyCtxType a2
    -- InstRPair
    go _ (ZPair a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      context
        %= solveExistential
          (ZPair (ZExistential alphaHat1) (ZExistential alphaHat2))
          alphaHat
      (`instantiateR` alphaHat1) =<< applyCtxType a1
      (`instantiateR` alphaHat2) =<< applyCtxType a2
    -- InstRAllL
    go _ (ZForall beta b) = do
      markExtential $ \betaHat -> do
        let b' = (ZExistential betaHat `substitute` ZUniversal beta) b
        b' `instantiateR` alphaHat
    --
    go _ tau = bug $ NotMonotype tau

check' :: (Monoid l, MonadState CheckerState m) => Untyped l -> ZType -> m (Typed l)
-- 1|
check' (EUnit :@ l) ZUnit = pure (EUnit :@ l)
-- ∀|
check' e (ZForall alpha a) = withUniversal alpha $ e `check` a
-- ->|
check' (ELambda x e n () :@ l) z@(ZFunction a b) = do
  e' <- checkFunction x e a b
  applyCtxExpr (ELambda x e' n z :@ l)
check' (ELambda' xs e n () :@ l) z@(ZFunction a b) = do
  e' <- checkFunction' xs e a b
  applyCtxExpr (ELambda' xs e' n z :@ l)
check' (EImplicit x e n () :@ l) z@(ZFunction a b) = do
  e' <- checkFunction x e a b
  applyCtxExpr (ELambda x e' n z :@ l)
check' (EMacro x e () :@ l) z@(ZFunction a b) = do
  e'' <- checkFunction x e a b
  applyCtxExpr (EMacro x e'' z :@ l)
check' (EMacro' xs e () :@ l) z@(ZFunction a b) = do
  e'' <- checkFunction' xs e a b
  applyCtxExpr (EMacro' xs e'' z :@ l)
check' (ENative1 _ () :@ _) _ = bug Native
check' (ENative2 _ () :@ _) _ = bug Native
check' (ENativeIO _ () :@ _) _ = bug Native
check' (ESpecial () :@ _) _ = bug Special
-- ->Pair
check' (EPair e1 e2 () :@ l) (ZPair b1 b2) = do
  a1' <- e1 `check` b1
  a2' <- e2 `check` b2
  applyCtxExpr (EPair a1' a2' (ZPair (exprType a1') (exprType a2')) :@ l)
-- Sub
check' e b = do
  a <- synthesize e
  b' <- applyCtxType b
  exprType a `subtype` b'
  applyCtxExpr a

checkFunction ::
  (Monoid l, MonadState CheckerState m) => Variable -> Untyped l -> ZType -> ZType -> m (Typed l)
checkFunction x e a b = do
  context %= (CVariable x a <:)
  e' <- e `check` b
  context %= dropVar x
  pure e'

checkFunction' ::
  (Monoid l, MonadState CheckerState m) => [Variable] -> Untyped l -> ZType -> ZType -> m (Typed l)
checkFunction' xs e a b = do
  case maybeList a of
    Just ts | length xs == length ts -> do
      for_ (zip xs ts) $ \(x, t) -> context %= (CVariable x t <:)
      e' <- e `check` b
      for_ (reverse xs) $ \x -> context %= dropVar x
      pure e'
    _ -> bug $ LambdaMissmatch xs a

synthesize' :: (Monoid l, MonadState CheckerState m) => Untyped l -> m (Typed l)
-- Var
synthesize' (ESymbol a () :@ l) = do
  ctx <- use context
  case lookupVar (Variable a) ctx of
    Just t -> pure (ESymbol a t :@ l)
    Nothing -> bug $ UndefinedVariable (Variable a)
-- Anno
synthesize' (EAnnotation e a :@ l) = do
  e' <- e `check` a
  applyCtxExpr (EAnnotation e' a :@ l)
-- 1|=>
synthesize' (EUnit :@ l) = pure (EUnit :@ l)
-- ->|=>
synthesize' (ELambda x e n () :@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction x e
  applyCtxExpr (ELambda x e' n (ZFunction alphaHat betaHat) :@ l)
synthesize' (ELambda' xs e n () :@ l) = do
  (e', alphaHats, betaHat) <- synthesizeFunction' xs e
  applyCtxExpr (ELambda' xs e' n (ZFunction alphaHats betaHat) :@ l)
synthesize' (EImplicit x e n () :@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction x e
  applyCtxExpr (EImplicit x e' n (ZFunction alphaHat betaHat) :@ l)
synthesize' (EMacro x e () :@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction x e
  applyCtxExpr (EMacro x e' (ZFunction alphaHat betaHat) :@ l)
synthesize' (EMacro' xs e () :@ l) = do
  (e', alphaHats, betaHat) <- synthesizeFunction' xs e
  applyCtxExpr (EMacro' xs e' (ZFunction alphaHats betaHat) :@ l)
synthesize' (ENative1 _ () :@ _) = bug Native
synthesize' (ENative2 _ () :@ _) = bug Native
synthesize' (ENativeIO _ () :@ _) = bug Native
synthesize' (ESpecial () :@ _) = bug Special
-- ->E
synthesize' (EApply e1@(EImplicit _ _ _ _ :@ _) [] () :@ l) = do
  e1' <- synthesize e1
  case exprType e1' of
    ZFunction _ c -> applyCtxExpr (EApply e1' [] c :@ l)
    _ -> bug Impossible
synthesize' (EApply e1 e2 () :@ l) = do
  e1' <- synthesize e1
  (e2', c) <- exprType e1' `applySynth` fromList e2
  case maybeList e2' of
    Just e2'' -> applyCtxExpr (EApply e1' e2'' c :@ l)
    Nothing -> bug (NotList $ stripLocation e2')
synthesize' (EPair l r () :@ loc) = do
  l' <- synthesize l
  r' <- synthesize r
  pure (EPair l' r' (ZPair (exprType l') (exprType r')) :@ loc)
-- Type
synthesize' (EType m :@ l) = (:@ l) . EType <$> synthesizeType m
  where
    synthesizeType (ZForall u@(Universal s) t) = do
      let v = Variable s
      context %= (CVariable v (ZType 0) <:)
      t' <- synthesizeType t
      context %= dropVar v
      ZForall u <$> applyCtxType t'
    synthesizeType (ZFunction a b) = do
      a' <- synthesizeType a
      b' <- synthesizeType b
      pure (ZFunction a' b')
    synthesizeType (ZPair a b) = do
      a' <- synthesizeType a
      b' <- synthesizeType b
      pure (ZPair a' b')
    synthesizeType (ZUntyped e) = unwrapType <$> synthesize e
    synthesizeType (ZValue e) = bug (UnexpectedTyped e)
    synthesizeType z = pure z
-- Quote
synthesize' (EQuote x () :@ lq) =
  let z = (synthesizeQuoted x)
   in pure (EQuote z (exprType z) :@ lq)
  where
    synthesizeQuoted :: Untyped l -> Typed l
    synthesizeQuoted (EType n :@ loc) = EType n :@ loc
    synthesizeQuoted (EUnit :@ loc) = EUnit :@ loc
    synthesizeQuoted (ESymbol s () :@ loc) = ESymbol s ZSymbol :@ loc
    synthesizeQuoted (EPair l r () :@ loc) =
      let l' = synthesizeQuoted l
          r' = synthesizeQuoted r
       in EPair l' r' (ZPair (exprType l') (exprType r')) :@ loc
    synthesizeQuoted z = bug (NotQuotable $ stripLocation z)

synthesizeFunction ::
  (Monoid l, MonadState CheckerState m) => Variable -> Untyped l -> m (Typed l, ZType, ZType)
synthesizeFunction x e = do
  alphaHat <- ZExistential <$> nextExtential
  betaHat <- ZExistential <$> nextExtential
  context %= (CVariable x alphaHat <:)
  e' <- e `check` betaHat
  context %= dropVar x
  pure (e', alphaHat, betaHat)

synthesizeFunction' ::
  (Monoid l, MonadState CheckerState m) => [Variable] -> Untyped l -> m (Typed l, ZType, ZType)
synthesizeFunction' xs e = do
  alphaHats <- forM xs $ \x -> (x,) . ZExistential <$> nextExtential
  betaHat <- ZExistential <$> nextExtential
  for_ alphaHats $ \(x, alphaHat) ->
    context %= (CVariable x alphaHat <:)
  e' <- e `check` betaHat
  for_ (reverse alphaHats) $ \(x, _) ->
    context %= dropVar x
  pure (e', fromList (snd <$> alphaHats), betaHat)

applySynth' :: (Monoid l, MonadState CheckerState m) => ZType -> Untyped l -> m (Typed l, ZType)
-- ∀App
applySynth' (ZForall alpha a) e = do
  alphaHat <- nextExtential
  let a' = (ZExistential alphaHat `substitute` ZUniversal alpha) a
  a' `applySynth` e
-- alphaHatApp
applySynth' (ZExistential alphaHat) e = do
  (alphaHat2, alphaHat1) <- withHole alphaHat $ do
    a2 <- nextExtential
    a1 <- nextExtential
    pure (a2, a1)
  let f = ZFunction (ZExistential alphaHat1) (ZExistential alphaHat2)
  context %= solveExistential f alphaHat
  e' <- e `check` ZExistential alphaHat1
  (e',) <$> applyCtxType (ZExistential alphaHat2)
-- ->App
applySynth' (ZFunction a c) e = do
  e' <- e `check` a
  (e',) <$> applyCtxType c
--
applySynth' t e = bug $ CannotApply t (stripLocation e)
