{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Zaphod where

import Lens.Micro.Mtl
import System.IO.Unsafe (unsafePerformIO)
import Text.Megaparsec (errorBundlePretty, parse)
import Zaphod.Base
import Zaphod.Context
import Zaphod.Parser
import Zaphod.Types

data ZaphodError
  = UndefinedVariable Variable
  | TypeError Text
  deriving (Show)

instance Exception ZaphodError

data ZaphodBug
  = MissingSubtypeCase ZType ZType Context
  | MissingApplySynthCase ZType Untyped Context
  | NotMonotype ZType
  | InvalidApply Untyped
  deriving (Show)

instance Exception ZaphodBug

debug :: Bool
debug = True

traceM' :: Applicative f => Text -> f ()
traceM' x = do
  when debug . traceM $ toString x

emptyZState :: ZState
emptyZState =
  ZState
    { _context = baseContext,
      _existentialData = 'α'
    }

nextExtential :: (MonadState ZState m) => m Existential
nextExtential = do
  c <- existentialData <<%= succ
  let n = Existential $ toText [c]
  context %= (CUnsolved n <:)
  pure n

markExtential :: (MonadState ZState m) => (Existential -> m a) -> m a
markExtential x = do
  c <- existentialData <<%= succ
  let n = Existential $ toText [c]
  context %= (CMarker n <:)
  context %= (CUnsolved n <:)
  res <- x n
  context %= dropMarker n
  pure res

withHole :: (MonadState ZState m) => Existential -> m a -> m a
withHole e x = do
  (h, ctx) <- wind e <$> use context
  context .= ctx
  res <- x
  context %= unwind h
  pure res

withUniversal :: (MonadState ZState m) => Universal -> m a -> m a
withUniversal alpha x = do
  context %= (CUniversal alpha <:)
  res <- x
  context %= dropUniversal alpha
  pure res

applyCtxType :: ZType -> State ZState ZType
applyCtxType z@(ZUniversal _) = pure z
applyCtxType ZUnit = pure ZUnit
applyCtxType ZSymbol = pure ZSymbol
applyCtxType z@(ZExistential x) = do
  ctx <- use context
  case lookupType x ctx of
    RSolved t -> pure t
    RUnsolved -> pure z
    RMissing -> bug (MissingExistentialInContext x ctx)
applyCtxType (ZFunction a b) = ZFunction <$> applyCtxType a <*> applyCtxType b
applyCtxType (ZForall a t) = ZForall a <$> applyCtxType t

applyCtxExpr :: Typed -> State ZState Typed
applyCtxExpr = traverse applyCtxType

exprType :: Typed -> ZType
exprType EUnit = ZUnit
exprType (ELambda _ _ t) = t
exprType (EAnnotation _ t) = t
exprType (ESymbol _ t) = t
exprType (EPair _ _ t) = t

notInFV :: Existential -> ZType -> Bool
notInFV _ ZUnit = True
notInFV _ (ZUniversal _) = True
notInFV a (ZExistential b) = a /= b
notInFV a (ZForall _ b) = notInFV a b
notInFV a (ZFunction b c) = notInFV a b && notInFV a c
notInFV _ ZSymbol = True

isMonoType :: ZType -> Bool
isMonoType ZUnit = True
isMonoType ZSymbol = True
isMonoType (ZUniversal _) = True
isMonoType (ZExistential _) = True
isMonoType (ZFunction _ _) = True
isMonoType _ = False

subtype :: ZType -> ZType -> State ZState ()
subtype a b = do
  ctx <- use context
  traceM' ("<sub " <> render a <> " <: " <> render b)
  traceM' ("     " <> render ctx)
  subtype' a b
  ctx' <- use context
  traceM' ("     " <> render ctx')

instantiateL :: Existential -> ZType -> State ZState ()
instantiateL a b = do
  ctx <- use context
  traceM' ("<inL " <> render a <> " <: " <> render b)
  traceM' ("     " <> render ctx)
  instantiateL' a b
  ctx' <- use context
  traceM' (">    " <> render ctx')

instantiateR :: ZType -> Existential -> State ZState ()
instantiateR a b = do
  ctx <- use context
  traceM' ("<inR " <> render a <> " := " <> render b)
  traceM' ("     " <> render ctx)
  instantiateR' a b
  ctx' <- use context
  traceM' (">    " <> render ctx')

check :: Untyped -> ZType -> State ZState Typed
check a b = do
  ctx <- use context
  traceM' ("<chk " <> render a <> " =: " <> render b)
  traceM' ("     " <> render ctx)
  res <- check' a b
  ctx' <- use context
  traceM' (">    " <> render ctx')
  pure res

synthesize :: Untyped -> State ZState Typed
synthesize a = do
  ctx <- use context
  traceM' ("<syn " <> render a)
  traceM' ("     " <> render ctx)
  res <- synthesize' a
  ctx' <- use context
  traceM' (">    " <> render res)
  traceM' ("     " <> render ctx')
  pure res

applySynth :: ZType -> Untyped -> State ZState (Typed, ZType)
applySynth a b = do
  ctx <- use context
  traceM' ("<app " <> render a <> " =>> " <> render b)
  traceM' ("     " <> render ctx)
  res <- applySynth' a b
  ctx' <- use context
  traceM' (">    " <> render res)
  traceM' ("     " <> render ctx')
  pure res

subtype' :: ZType -> ZType -> State ZState ()
-- <:Var
subtype' (ZUniversal alpha) (ZUniversal beta) | alpha == beta = pass
-- <:Unit
subtype' ZUnit ZUnit = pass
-- <:Exvar
subtype' (ZExistential alphaHat) (ZExistential betaHat) | alphaHat == betaHat = pass
-- <:->
subtype' (ZFunction a1 a2) (ZFunction b1 b2) = do
  b1 `subtype` a1
  a2 `subtype` b2
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
--
subtype' a b = bug $ TypeError (render a <> " is not a subtype of " <> render b)

instantiateL' :: Existential -> ZType -> State ZState ()
-- InstLReach
instantiateL' alphaHat (ZExistential betaHat) =
  context %= solveExistential (ZExistential alphaHat) betaHat
-- InstLArr
instantiateL' alphaHat (ZFunction a1 a2) = do
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
-- InstLAllR
instantiateL' alphaHat (ZForall beta b) = do
  withUniversal beta $ do
    alphaHat `instantiateL` b
-- InstLSolve
instantiateL' alphaHat tau = do
  if isMonoType tau
    then context %= solveExistential tau alphaHat
    else bug $ NotMonotype tau

instantiateR' :: ZType -> Existential -> State ZState ()
-- InstRReach
instantiateR' betaHat@(ZExistential _) alphaHat = do
  context %= solveExistential betaHat alphaHat
-- InstRArr
instantiateR' (ZFunction a1 a2) alphaHat = do
  (alphaHat1, alphaHat2) <-
    withHole alphaHat $ do
      e1 <- nextExtential
      e2 <- nextExtential
      pure (e1, e2)
  context
    %= solveExistential
      (ZFunction (ZExistential alphaHat1) (ZExistential alphaHat2))
      alphaHat
  alphaHat1 `instantiateL` a1
  a2 `instantiateR` alphaHat2
-- InstRAllL
instantiateR' (ZForall beta b) alphaHat = do
  markExtential $ \betaHat -> do
    let b' = (ZExistential betaHat `substitute` ZUniversal beta) b
    b' `instantiateR` alphaHat
-- InstRSolve
instantiateR' tau alphaHat =
  if isMonoType tau
    then context %= solveExistential tau alphaHat
    else bug $ NotMonotype tau

check' :: Untyped -> ZType -> State ZState Typed
-- 1|
check' EUnit ZUnit = pure EUnit
-- ∀|
check' e (ZForall alpha a) = withUniversal alpha $ e `check` a
-- ->|
check' (ELambda x e ()) z@(ZFunction a b) = do
  context %= (CVariable x a <:)
  e' <- e `check` b
  e'' <- applyCtxExpr e'
  context %= dropVar x
  pure (ELambda x e'' z)
-- Sub
check' e b = do
  a <- synthesize e
  a' <- applyCtxExpr a
  b' <- applyCtxType b
  exprType a' `subtype` b'
  applyCtxExpr a

synthesize' :: Untyped -> State ZState Typed
-- Var
synthesize' (ESymbol a ()) = do
  ctx <- use context
  case lookupVar (Variable a) ctx of
    Just t -> pure $ ESymbol a t
    Nothing -> bug $ UndefinedVariable (Variable a)
-- Anno
synthesize' (EAnnotation e a) = do
  e' <- e `check` a
  applyCtxExpr e'
-- 1|=>
synthesize' EUnit = pure EUnit
-- ->|=>
synthesize' (ELambda x e ()) = do
  alphaHat <- ZExistential <$> nextExtential
  betaHat <- ZExistential <$> nextExtential
  context %= (CVariable x alphaHat <:)
  e' <- e `check` betaHat
  context %= dropVar x
  applyCtxExpr (ELambda x e' (ZFunction alphaHat betaHat))
-- ->E
synthesize' (EPair e1 (EPair e2 rs ()) ())
  | isList rs = do
    e1' <- synthesize e1
    (e2', c) <- exprType e1' `applySynth` e2
    pure $ EPair e1' e2' c
synthesize' p@(EPair _ _ ()) = bug (InvalidApply p)

applySynth' :: ZType -> Untyped -> State ZState (Typed, ZType)
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
  (,) <$> applyCtxExpr e' <*> applyCtxType (ZExistential alphaHat2)
-- ->App
applySynth' (ZFunction a c) e = do
  e' <- e `check` a
  (,) <$> applyCtxExpr e' <*> applyCtxType c
--
applySynth' t e = do
  ctx <- use context
  bug $ MissingApplySynthCase t e ctx

test :: IO ()
test = do
  print' (parseTest unit)
  print' (parseTest pair)
  print' (parseTest lambda)
  print' (parseTest lambdaU)
  print' (parseTest lambda2)
  print' (parseTest appLambda)
  putStrLn "-"
  print' (synthesized unit)
  -- print (synthesized pair)
  -- putStrLn ""
  print' (synthesized lambda)
  print' (synthesized lambdaU)
  print' (synthesized lambda2)
  putStrLn "--------"
  print' (synthesized appLambda)
  where
    print' :: (Render a) => a -> IO ()
    print' = putStrLn . toString . render
    --
    unit = "()"
    pair = "(().())"
    lambda = "(\\x.x)"
    lambdaU = "(\\x.())"
    lambda2 = "(\\x.(\\y.x))"
    appLambda = "((\\x.x) ())"
    -- lambda2p = "(\\x.(\\y.(x.y)))"
    parseTest t = unsafePerformIO $ case parse token "" t of
      Left e -> die (errorBundlePretty e)
      Right v -> pure v
    synthesized a = evalState (synthesize $ parseTest a) emptyZState
