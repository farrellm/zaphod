{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Checker (check, synthesize, subtype) where

import Data.MonoTraversable (otraverse)
import qualified Data.Text as T
import Lens.Micro.Mtl (use, (%=), (+=), (-=), (.=), (<<%=))
import Zaphod.Context
import Zaphod.Types

type MonadChecker l m =
  ( MonadState CheckerState m,
    MonadError (CheckerException l) m,
    CTyped l,
    CUntyped l
  )

bind2 :: (Monad m) => (a -> b -> m c) -> m a -> m b -> m c
bind2 f x y = do
  x' <- x
  y' <- y
  f x' y'

nextExtential :: (MonadState CheckerState m) => m Existential
nextExtential = do
  c <- existentialData <<%= next
  let n = Existential $ fromString [c]
  context %= (CUnsolved n <:)
  pure n

markExtential :: (MonadState CheckerState m) => (Existential -> m a) -> m a
markExtential x = do
  c <- existentialData <<%= next
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
applyCtxType ZAny = pure ZAny
applyCtxType z@(ZUniversal _) = pure z
applyCtxType ZUnit = pure ZUnit
applyCtxType ZSymbol = pure ZSymbol
applyCtxType z@(ZExistential x) = do
  ctx <- use context
  case lookupType x ctx of
    RSolved t -> pure t
    _ -> pure z
applyCtxType (ZFunction a b) = ZFunction <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZImplicit a b) = ZImplicit <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZPair a b) = ZPair <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZForall a t) = ZForall a <$> applyCtxType t
applyCtxType (ZValue x) = ZValue <$> applyCtxExpr x
applyCtxType z@(ZUntyped _) = pure z

applyCtxExpr :: (MonadState CheckerState m, CTyped l) => Typed l -> m (Typed l)
applyCtxExpr (EType t :@@ l) = (:@@ l) . EType <$> applyCtxType t
applyCtxExpr (EAnnotation e t :@@ l) = (:@@ l) <$> (EAnnotation <$> applyCtxExpr e <*> applyCtxType t)
applyCtxExpr x = otraverse applyCtxType x

notInFV :: Existential -> ZType -> Bool
notInFV _ (ZType _) = True
notInFV _ ZAny = True
notInFV _ ZUnit = True
notInFV _ (ZUniversal _) = True
notInFV a (ZExistential b) = a /= b
notInFV a (ZForall _ b) = notInFV a b
notInFV a (ZFunction b c) = notInFV a b && notInFV a c
notInFV a (ZImplicit b c) = notInFV a b && notInFV a c
notInFV a (ZPair b c) = notInFV a b && notInFV a c
notInFV _ ZSymbol = True
notInFV a (ZValue x) = notInFV a (exprType x)
notInFV _ (ZUntyped _) = bug Unreachable

isMonoType :: ZType -> Bool
isMonoType ZAny = True
isMonoType ZUnit = True
isMonoType ZSymbol = True
isMonoType (ZUniversal _) = True
isMonoType (ZExistential _) = True
isMonoType (ZType _) = True
isMonoType (ZFunction a b) = isMonoType a && isMonoType b
isMonoType (ZImplicit a b) = isMonoType a && isMonoType b
isMonoType (ZPair a b) = isMonoType a && isMonoType b
isMonoType (ZValue v) = isMonoTypeValue v
  where
    isMonoTypeValue (LocU (EType t)) = isMonoType t
    isMonoTypeValue (LocU EUnit) = True
    isMonoTypeValue (LocU (ESymbol _ t)) = isMonoType t
    isMonoTypeValue (LocU (ELambda1 _ h _ _)) = isMonoTypeValue h
    isMonoTypeValue (LocU (ELambdaN _ h _ _)) = isMonoTypeValue h
    isMonoTypeValue (LocU (EImplicit _ h _ _)) = isMonoTypeValue h
    isMonoTypeValue (LocU (EApply1 f x _)) = isMonoTypeValue f && isMonoTypeValue x
    isMonoTypeValue (LocU (EApplyN f xs _)) = isMonoTypeValue f && all isMonoTypeValue xs
    isMonoTypeValue (LocU (EPair l r _)) = isMonoTypeValue l && isMonoTypeValue r
    isMonoTypeValue (LocU (EAnnotation x _)) = isMonoTypeValue x
    isMonoTypeValue (LocU (EQuote _ _)) = True
    isMonoTypeValue e = bug (NotImplemented $ render e)
isMonoType (ZForall _ _) = False
isMonoType (ZUntyped _) = bug Unreachable

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

subtype :: (MonadChecker () m) => ZType -> ZType -> m ()
subtype a b =
  logInfo ("sub " <> render a <> " <: " <> render b) $
    subtype' a b

instantiateL :: (MonadChecker l m) => Existential -> ZType -> m ()
instantiateL a b =
  logInfo ("inL " <> render a <> " =: " <> render b) $
    instantiateL' a b

instantiateR :: (MonadChecker l m) => ZType -> Existential -> m ()
instantiateR a b =
  logInfo ("inR " <> render a <> " := " <> render b) $
    instantiateR' a b

check :: (MonadChecker l m) => Untyped l -> ZType -> m (Typed l)
check a b =
  logInfo ("chk " <> render a <> " =: " <> render b) $
    check' a b

synthesize :: (MonadChecker l m) => Untyped l -> m (Typed l)
synthesize a =
  logInfo ("syn " <> render a) $
    synthesize' a

applySynth :: (MonadChecker l m) => ZType -> Untyped l -> m (ZType, Typed l, ZType)
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

subtype' :: (MonadChecker () m) => ZType -> ZType -> m ()
-- <:Any
subtype' _ ZAny = pass
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
subtype' (ZImplicit a1 a2) (ZImplicit b1 b2) = do
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
subtype' (ZValue a) (ZValue b) | a == b = pass
--
subtype' a b = throwError $ NotSubtype a b ()

instantiateL' :: (MonadChecker l m) => Existential -> ZType -> m ()
instantiateL' alphaHat x = do
  d <-
    if isMonoType x
      then isDeeper x alphaHat
      else pure False
  -- traceShowM d
  go d x
  where
    -- InstLSolve
    go True tau = solveExistential tau alphaHat
    -- InstLReach
    go _ (ZExistential betaHat) =
      solveExistential (ZExistential alphaHat) betaHat
    -- InstLArr
    go _ (ZFunction a1 a2) = goFunction ZFunction a1 a2
    go _ (ZImplicit a1 a2) = goFunction ZImplicit a1 a2
    -- InstLPair
    go _ (ZPair a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      solveExistential
        (ZPair (ZExistential alphaHat1) (ZExistential alphaHat2))
        alphaHat
      (alphaHat1 `instantiateL`) =<< applyCtxType a1
      (alphaHat2 `instantiateL`) =<< applyCtxType a2
    -- InstLAllR
    go _ (ZForall beta b) =
      withUniversal beta $
        alphaHat `instantiateL` b
    --
    go _ _ = bug Unreachable

    goFunction f a1 a2 = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e2 <- nextExtential
          e1 <- nextExtential
          pure (e1, e2)
      solveExistential
        (f (ZExistential alphaHat1) (ZExistential alphaHat2))
        alphaHat
      (`instantiateR` alphaHat1) =<< applyCtxType a1
      (alphaHat2 `instantiateL`) =<< applyCtxType a2

instantiateR' :: (MonadChecker l m) => ZType -> Existential -> m ()
instantiateR' x alphaHat = do
  d <-
    if isMonoType x
      then isDeeper x alphaHat
      else pure False
  go d x
  where
    -- InstRSolve
    go True tau = solveExistential tau alphaHat
    -- InstRReach
    go _ (ZExistential betaHat) = solveExistential (ZExistential alphaHat) betaHat
    -- InstRArr
    go _ (ZFunction a1 a2) = goFunction ZFunction a1 a2
    go _ (ZImplicit a1 a2) = goFunction ZImplicit a1 a2
    -- InstRPair
    go _ (ZPair a1 a2) = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      solveExistential
        (ZPair (ZExistential alphaHat1) (ZExistential alphaHat2))
        alphaHat
      (`instantiateR` alphaHat1) =<< applyCtxType a1
      (`instantiateR` alphaHat2) =<< applyCtxType a2
    -- InstRAllL
    go _ (ZForall beta b) =
      markExtential $ \betaHat ->
        let b' = (ZExistential betaHat `substitute` ZUniversal beta) b
         in b' `instantiateR` alphaHat
    --
    go _ _ = bug Unreachable

    goFunction f a1 a2 = do
      (alphaHat1, alphaHat2) <-
        withHole alphaHat $ do
          e1 <- nextExtential
          e2 <- nextExtential
          pure (e1, e2)
      solveExistential
        (f (ZExistential alphaHat1) (ZExistential alphaHat2))
        alphaHat
      (alphaHat1 `instantiateL`) =<< applyCtxType a1
      (`instantiateR` alphaHat2) =<< applyCtxType a2

check' :: (MonadChecker l m) => Untyped l -> ZType -> m (Typed l)
-- 1|
check' (EUnit :@@ l) ZUnit = pure (EUnit :@@ l)
-- ∀|
check' e (ZForall alpha a) = withUniversal alpha $ e `check` a
-- ->|
check' (ELambda1 x e _ () :@@ l) z@(ZFunction a b) = do
  e' <- checkFunction1 x e a b
  applyCtxExpr (ELambda1 x e' mempty z :@@ l)
check' (ELambdaN xs e _ () :@@ l) z@(ZFunction a b)
  | Just cs <- maybeList a,
    length xs == length cs =
    do
      e' <- checkFunctionN xs e cs b
      applyCtxExpr (ELambdaN xs e' mempty z :@@ l)
check' (EImplicit x e _ () :@@ l) z@(ZImplicit a b) = do
  e' <- checkFunction1 x e a b
  applyCtxExpr (EImplicit x e' mempty z :@@ l)
check' (EMacro1 x e () :@@ l) z@(ZFunction a b) = do
  e'' <- checkFunction1 x e a b
  applyCtxExpr (EMacro1 x e'' z :@@ l)
check' (EMacroN xs e () :@@ l) z@(ZFunction a b)
  | Just cs <- maybeList a,
    length xs == length cs =
    do
      e' <- checkFunctionN xs e cs b
      applyCtxExpr (EMacroN xs e' z :@@ l)
check' (ENative _ () :@@ _) _ = bug Unreachable
check' (ENative' _ () :@@ _) _ = bug Unreachable
check' (ENativeIO _ () :@@ _) _ = bug Unreachable
check' (ESpecial () :@@ _) _ = bug Unreachable
-- ->Pair
check' (EPair e1 e2 () :@@ l) (ZPair b1 b2) = do
  a1' <- e1 `check` b1
  a2' <- e2 `check` b2
  applyCtxExpr (EPair a1' a2' (ZPair (exprType a1') (exprType a2')) :@@ l)
-- Sub
check' e b = do
  a <- synthesize e
  b' <- applyCtxType b
  mapError (const (location e) <$>) $ exprType a `subtype` b'
  applyCtxExpr a

checkFunction1 :: (MonadChecker l m) => Variable -> Untyped l -> ZType -> ZType -> m (Typed l)
checkFunction1 x e a b = do
  context %= (CVariable x a <:)
  e' <- e `check` b
  context %= dropVar x
  pure e'

checkFunctionN :: (MonadChecker l m) => [Variable] -> Untyped l -> [ZType] -> ZType -> m (Typed l)
checkFunctionN xs e cs b = do
  for_ (zip xs cs) $ \(x, c) ->
    context %= (CVariable x c <:)
  e' <- e `check` b
  for_ (reverse xs) $ \x ->
    context %= dropVar x
  pure e'

synthesize' :: (MonadChecker l m) => Untyped l -> m (Typed l)
-- Var
synthesize' (ESymbol a () :@@ l) = do
  ctx <- use context
  case lookupVar (Variable a) ctx of
    Just t -> pure (ESymbol a t :@@ l)
    Nothing -> throwError $ UndefinedVariable (Variable a)
-- Anno
synthesize' (EAnnotation e a :@@ l) = do
  e' <- e `check` a
  applyCtxExpr (EAnnotation e' a :@@ l)
-- 1|=>
synthesize' (EUnit :@@ l) = pure (EUnit :@@ l)
-- ->|=>
synthesize' (ELambda1 x e _ () :@@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction1 x e
  applyCtxExpr (ELambda1 x e' mempty (ZFunction alphaHat betaHat) :@@ l)
synthesize' (ELambdaN xs e _ () :@@ l) = do
  (e', alphaHats, betaHat) <- synthesizeFunctionN xs e
  applyCtxExpr (ELambdaN xs e' mempty (ZFunction (typeTuple alphaHats) betaHat) :@@ l)
synthesize' (EImplicit x e _ () :@@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction1 x e
  applyCtxExpr (EImplicit x e' mempty (ZImplicit alphaHat betaHat) :@@ l)
synthesize' (EMacro1 x e () :@@ l) = do
  (e', alphaHat, betaHat) <- synthesizeFunction1 x e
  applyCtxExpr (EMacro1 x e' (ZFunction alphaHat betaHat) :@@ l)
synthesize' (EMacroN xs e () :@@ l) = do
  (e', alphaHats, betaHat) <- synthesizeFunctionN xs e
  applyCtxExpr (EMacroN xs e' (ZFunction (typeTuple alphaHats) betaHat) :@@ l)
synthesize' (ENative _ () :@@ _) = bug Unreachable
synthesize' (ENative' _ () :@@ _) = bug Unreachable
synthesize' (ENativeIO _ () :@@ _) = bug Unreachable
synthesize' (ESpecial () :@@ _) = bug Unreachable
-- ->E
synthesize' (EApply1 e1 e2 () :@@ l) = do
  e1' <- synthesize e1
  (ze1'', e2', c) <- exprType e1' `applySynth` e2
  applyCtxExpr (EApply1 (setType ze1'' e1') e2' c :@@ l)
synthesize' (EApplyN e1 e2s () :@@ l) = do
  e1' <- synthesize e1
  (ze1'', e2', c) <- exprType e1' `applySynth` tuple e2s
  case nonEmpty =<< maybeList e2' of
    Just e2s' -> applyCtxExpr (EApplyN (setType ze1'' e1') e2s' c :@@ l)
    Nothing -> bug Unreachable
synthesize' (EPair l r () :@@ loc) = do
  l' <- synthesize l
  r' <- synthesize r
  pure (EPair l' r' (ZPair (exprType l') (exprType r')) :@@ loc)
-- Type
synthesize' (EType m :@@ l) = (:@@ l) . EType <$> synthesizeType m
  where
    synthesizeType (ZForall u@(Universal s) t) = do
      k <- ZExistential <$> nextExtential
      let v = Variable s
      context %= (CVariable v k <:)
      t' <- synthesizeType t
      context %= dropVar v
      ZForall u <$> applyCtxType t'
    synthesizeType (ZFunction a b) = do
      a' <- synthesizeType a
      b' <- synthesizeType b
      pure (ZFunction a' b')
    synthesizeType (ZImplicit a b) = do
      a' <- synthesizeType a
      b' <- synthesizeType b
      pure (ZImplicit a' b')
    synthesizeType (ZPair a b) = do
      a' <- synthesizeType a
      b' <- synthesizeType b
      pure (ZPair a' b')
    synthesizeType (ZUntyped e) = unwrapType . stripLocation <$> synthesize (setLocation l e)
    synthesizeType (ZValue _) = bug Unreachable
    synthesizeType z = pure z
-- Quote
synthesize' (EQuote x () :@@ lq) =
  let z = synthesizeQuoted x
   in pure (EQuote z (exprType z) :@@ lq)
  where
    synthesizeQuoted (EType n :@@ loc) = EType n :@@ loc
    synthesizeQuoted (EUnit :@@ loc) = EUnit :@@ loc
    synthesizeQuoted (ESymbol s () :@@ loc) = ESymbol s ZSymbol :@@ loc
    synthesizeQuoted (EPair l r () :@@ loc) =
      let l' = synthesizeQuoted l
          r' = synthesizeQuoted r
       in EPair l' r' (ZPair (exprType l') (exprType r')) :@@ loc
    synthesizeQuoted _ = bug Unreachable

synthesizeFunction1 :: (MonadChecker l m) => Variable -> Untyped l -> m (Typed l, ZType, ZType)
synthesizeFunction1 x e = do
  alphaHat <- ZExistential <$> nextExtential
  betaHat <- ZExistential <$> nextExtential
  context %= (CVariable x alphaHat <:)
  e' <- e `check` betaHat
  context %= dropVar x
  pure (e', alphaHat, betaHat)

synthesizeFunctionN :: (MonadChecker l m) => [Variable] -> Untyped l -> m (Typed l, [ZType], ZType)
synthesizeFunctionN xs e = do
  alphaHats <- forM xs $ \x -> do
    alphaHat <- ZExistential <$> nextExtential
    pure (x, alphaHat)
  betaHat <- ZExistential <$> nextExtential
  for_ alphaHats $ \(x, alphaHat) ->
    context %= (CVariable x alphaHat <:)
  e' <- e `check` betaHat
  for_ (reverse xs) $ \x ->
    context %= dropVar x
  pure (e', snd <$> alphaHats, betaHat)

applySynth' :: (MonadChecker l m) => ZType -> Untyped l -> m (ZType, Typed l, ZType)
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
  solveExistential f alphaHat
  e' <- e `check` ZExistential alphaHat1
  f' <- applyCtxType f
  c' <- applyCtxType (ZExistential alphaHat2)
  pure (f', e', c')
-- ->App
applySynth' f@(ZFunction a c) e = do
  e' <- e `check` a
  f' <- applyCtxType f
  c' <- applyCtxType c
  pure (f', e', c')
applySynth' (ZImplicit a c) e = do
  (f', e', c') <- c `applySynth` e
  a' <- applyCtxType a
  pure (ZImplicit a' f', e', c')
--
applySynth' t e = throwError $ CannotApply t (stripLocation e) (location e)
