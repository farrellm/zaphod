{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator
  ( evaluate,
    evaluateType,
    evaluateTopLevel,
    analyzeUntyped,
    macroExpand,
    liftChecker,
  )
where

import Control.Monad.Except (liftEither)
import qualified Data.Map as M
import qualified Data.Set as S
import Lens.Micro.Mtl ((%=))
import Relude.Extra.Map ((!?))
import Zaphod.Base
import Zaphod.Checker
import Zaphod.Context
import Zaphod.Types

type MonadEvaluator l m =
  ( Monoid l,
    MonadReader Environment m,
    MonadError (EvaluatorException l) m,
    MonadIO m
  )

liftChecker ::
  (MonadError (EvaluatorException l) m) =>
  (a -> ExceptT (CheckerException l) m b) ->
  a ->
  m b
liftChecker f x = do
  e <- runExceptT $ f x
  case e of
    Right res -> pure res
    Left err -> throwError (CheckerException err)

liftNative :: (MonadError (EvaluatorException ()) m) => Either NativeException a -> m a
liftNative = liftEither . first (NativeException ())

evaluate :: (MonadEvaluator l m) => Typed l -> m (Typed ())
evaluate expr = do
  env <- ask
  runReaderT (eval expr) (mempty, env)
  where
    eval ::
      ( Monoid k,
        MonadReader (Environment, Environment) m,
        MonadError (EvaluatorException k) m,
        MonadIO m
      ) =>
      Typed k ->
      m (Typed ())
    eval (ESymbol s z :@ _) = do
      (m, n) <- bimapF (!? s) (!? s) ask
      pure $ case (m, n) of
        (Just v, _) -> setType z v
        (_, Just v) -> setType z v
        (_, _) -> bug Unreachable
    eval (EAnnotation v z :@ _) = setType z <$> eval v
    eval (EApply (ESymbol "if" _ :@ _) xs _ :@ _) =
      case xs of
        [p, a, b] -> do
          p' <- eval p
          if p' == zTrue
            then eval a
            else eval b
        _ -> bug Unreachable
    eval (EApply (ESymbol "apply" _ :@ _) [f, xs] r :@ l) = do
      f' <- eval f
      xs' <- eval xs
      setType r <$> case (f', maybeList xs') of
        (ELambda (Variable v) e env _ :@ _, _) ->
          local (\(_, n) -> (M.insert v xs' env, n)) . errorLocation l $ eval e
        (EImplicit (Variable v) e env _ :@ _, _) ->
          local (\(_, n) -> (M.insert v xs' env, n)) . errorLocation l $ eval e
        (ENative1 (Native1 g) _ :@ _, Just [a]) ->
          errorLocation l . liftNative $ g a
        (ENative2 (Native2 g) _ :@ _, Just [a, b]) ->
          errorLocation l . liftNative $ g a b
        _ -> bug Unreachable
    eval (EApply f x r :@ l) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda (Variable v) e env _ :@ _ -> do
          x' <- eval x
          local (\(_, n) -> (M.insert v x' env, n)) . errorLocation l $ eval e
        EImplicit (Variable v) e env (ZImplicit i _) :@ _ -> do
          (a, b) <- bimapF (findOfType i) (findOfType i) ask
          case M.toList a ++ M.toList b of
            [(_, s)] ->
              local (\(_, n) -> (M.insert v s env, n)) $
                eval (EApply (setLocation (location f) e) x r :@ l)
            [] -> throwError (NoMatches i)
            ss -> throwError (MultipleMatches i (snd <$> ss))
        ENative1 (Native1 g) _ :@ _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a] -> errorLocation l . liftNative $ g a
            _ -> bug Unreachable
        ENative2 (Native2 g) _ :@ _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a, b] -> errorLocation l . liftNative $ g a b
            _ -> bug Unreachable
        ENativeIO (NativeIO g) _ :@ _ -> do
          x' <- eval x
          case maybeList x' of
            Just [] -> liftIO g
            _ -> bug Unreachable
        _ -> bug Unreachable
      where
        findOfType z = M.filter ((z ==) . exprType)
    eval (EPair a b t :@ _) = (:@ ()) <$> (EPair <$> eval a <*> eval b <*> pure t)
    eval (ELambda v e _ t :@ _) = (:@ ()) <$> (ELambda v (stripLocation e) <$> (fst <$> ask) <*> pure t)
    eval (EQuote z _ :@ _) = pure (stripLocation z)
    eval (EType t :@ l) = (:@ ()) . EType <$> errorLocation l (evalType t)
    eval e = pure (stripLocation e)
    --
    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (first (M.insert s (EType (ZUniversal u) :@ ()))) (evalType z)
    evalType (ZFunction a b) = ZFunction <$> evalType a <*> evalType b
    evalType (ZImplicit a b) = ZImplicit <$> evalType a <*> evalType b
    evalType (ZPair a b) = ZPair <$> evalType a <*> evalType b
    evalType (ZValue a) = unwrapType <$> eval a
    evalType (ZUntyped _) = bug Unreachable
    evalType z = pure z

evaluateType :: (MonadEvaluator l m) => Untyped l -> m ZType
evaluateType u = do
  env <- ask
  t <- evaluatingStateT (emptyCheckerState env) $ liftChecker (check u) (ZType 0)
  setExprType . unwrapType <$> evaluate t
  where
    setExprType (ZValue e) = ZValue (setType (ZType 0) e)
    setExprType z = z

analyzeType :: (MonadEvaluator l m) => Raw l -> m ZType
analyzeType RU = pure ZUnit
analyzeType x@(RS _) = ZUntyped . stripLocation <$> analyzeUntyped x
analyzeType (RS "_forall" :. RS u :. z :. RU) = ZForall (Universal u) <$> analyzeType z
analyzeType (RS "->" :. a :. b :. RU) = ZFunction <$> analyzeType a <*> analyzeType b
analyzeType (RS "=>" :. a :. b :. RU) = ZImplicit <$> analyzeType a <*> analyzeType b
analyzeType (RS "quote" :. x :. RU) =
  pure . ZUntyped $ EQuote (EType (quoteType x) :@ ()) () :@ ()
  where
    quoteType :: Raw l -> ZType
    quoteType RU = ZUnit
    quoteType (l :. r) = ZPair (quoteType l) (quoteType r)
    quoteType (RS s) = ZValue $ ESymbol s ZSymbol :@ ()
analyzeType (RPair (RSymbol "cons" :# lc) ts :# lp) =
  analyzeType (RPair (RSymbol "zcons" :# lc) ts :# lp)
analyzeType (a :. b) = do
  a' <- stripLocation <$> analyzeUntyped a
  case maybeList b of
    Just xs -> do
      xs' <- traverse (fmap (\z -> EType z :@ ()) . analyzeType) xs
      pure $ ZUntyped (EApply a' (fromList xs') () :@ ())
    Nothing -> do
      b' <- analyzeType b
      pure $ ZUntyped (EApply a' (EType b' :@ ()) () :@ ())

analyzeQuoted :: Raw l -> Untyped l
analyzeQuoted (RUnit :# l) = EUnit :@ l
analyzeQuoted (RSymbol s :# l) = ESymbol s () :@ l
analyzeQuoted (RPair x y :# l) = EPair (analyzeQuoted x) (analyzeQuoted y) () :@ l

analyzeUntyped :: (MonadEvaluator l m) => Raw l -> m (Untyped l)
analyzeUntyped (RUnit :# l) = pure (EUnit :@ l)
analyzeUntyped (RSymbol s :# l) = pure $ ESymbol s () :@ l
analyzeUntyped (RS "_lambda" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (ELambda (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure ())
analyzeUntyped (RS "implicit" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (EImplicit (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure ())
analyzeUntyped (RS "_macro" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (EMacro (Variable x) <$> analyzeUntyped e <*> pure ())
analyzeUntyped (RS ":" `RPair` (t :. RS "Type" :. RU) :# l) =
  (:@ l) . EType <$> analyzeType t
analyzeUntyped (RS ":" `RPair` (e :. t :. RU) :# l) =
  (:@ l) <$> (EAnnotation <$> analyzeUntyped e <*> evaluateRawType t)
analyzeUntyped (RS "quote" `RPair` (x :. RU) :# l) =
  pure $ EQuote (analyzeQuoted x) () :@ l
analyzeUntyped (RPair a b :# l) =
  case maybeList b of
    Just xs ->
      (:@ l) <$> (EApply <$> analyzeUntyped a <*> (fromList <$> traverse analyzeUntyped xs) <*> pure ())
    Nothing -> (:@ l) <$> (EApply <$> analyzeUntyped a <*> analyzeUntyped b <*> pure ())

evaluateRaw ::
  (Monoid l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
  Maybe (Symbol, Raw l) ->
  Raw l ->
  m (Typed ())
evaluateRaw m x = do
  env <- _environment <$> get
  x' <-
    usingReaderT env
      . evaluatingStateT (emptyCheckerState env)
      $ case m of
        Just (n, RSymbol "Type" :# _) -> do
          context %= (CVariable (Variable n) (ZType 0) <:)
          (:@ ()) . EType <$> evaluateRawType x
        Just (n, t) -> do
          t' <- evaluateRawType t
          context %= (CVariable (Variable n) t' <:)
          r <- evaluate =<< liftChecker (flip check t') =<< analyzeUntyped x
          pure $ setType t' r
        Nothing -> evaluate =<< liftChecker synthesize =<< analyzeUntyped x
  pure (first universalize x')
  where
    universalize z =
      let es = unbound z
          us = universals z
          eus = mkEUMap (toList es) us ['a' ..]
       in flipfoldl' ZForall (replaceExt eus z) eus

    unbound (ZExistential e) = one e
    unbound (ZForall _ z) = unbound z
    unbound (ZFunction a b) = unbound a <> unbound b
    unbound (ZPair a b) = unbound a <> unbound b
    unbound (ZValue a) = unbound $ exprType a
    unbound _ = mempty :: Set Existential

    universals (ZForall u z) = one u <> universals z
    universals (ZFunction a b) = universals a <> universals b
    universals (ZPair a b) = universals a <> universals b
    universals (ZValue a) = universals $ exprType a
    universals _ = mempty :: Set Universal

    mkEUMap [] _ _ = mempty :: Map Existential Universal
    mkEUMap es@(e : es') us (c : cs)
      | Universal (fromString [c]) `S.notMember` us =
        one (e, Universal $ fromString [c]) <> mkEUMap es' us cs
      | otherwise = mkEUMap es us cs
    mkEUMap _ _ [] = bug Unreachable

    replaceExt eus (ZExistential e) = case M.lookup e eus of
      Just u -> ZUniversal u
      Nothing -> bug $ MissingExistential e
    replaceExt eus (ZForall u z) = ZForall u $ replaceExt eus z
    replaceExt eus (ZFunction a b) = ZFunction (replaceExt eus a) (replaceExt eus b)
    replaceExt eus (ZPair a b) = ZPair (replaceExt eus a) (replaceExt eus b)
    replaceExt eus (ZValue a) = ZValue $ setType (replaceExt eus $ exprType a) a
    replaceExt _ z = z

evaluateRawType :: (MonadEvaluator l m) => Raw l -> m ZType
evaluateRawType t = do
  t' <- analyzeType t
  errorLocation (location t) $ evaluateType (stripExpr t')
  where
    stripExpr (ZUntyped u) = u
    stripExpr z = EType z :@ ()

macroExpand1 :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand1 w = do
  env <- ask
  evaluatingStateT (emptyCheckerState env) $ go w
  where
    go (RPair a@(RSymbol s :# _) b :# lq) = do
      f <- M.lookup s <$> ask
      case f of
        Just (EMacro v e _ :@ ()) -> goMacro $ ELambda v (stripType e) mempty () :@ ()
        _ -> (:# lq) . RPair a <$> goInner b
      where
        goMacro l = do
          let f' = setLocation mempty l
          b' <- analyzeUntyped $ quote b
          x' <- evaluate =<< liftChecker synthesize (EApply f' b' () :@ lq)
          pure $ setLocation lq (toRaw x')
    go (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    go r = pure r

    goInner (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    goInner r = pure r

    quote e = ["quote", e]

    toRaw (EUnit :@ l) = RUnit :# l
    toRaw (ESymbol s _ :@ l) = RSymbol s :# l
    toRaw (EPair x y _ :@ l) = RPair (toRaw x) (toRaw y) :# l
    toRaw _ = bug Unreachable

macroExpand :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand w = do
  w' <- macroExpand1 w
  if stripLocation w == stripLocation w'
    then pure w
    else macroExpand w'

evaluateTopLevel' ::
  (Monoid l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
  Raw l ->
  m (Typed ())
evaluateTopLevel' (RS "def" :. RS s :. e :. RU) = do
  e' <- evaluateRaw Nothing e
  environment %= M.insert s e'
  pure (EUnit :@ ())
evaluateTopLevel' (RS "def" :. RS s :. t :. e :. RU) = do
  e' <- evaluateRaw (Just (s, t)) e
  environment %= M.insert s e'
  pure (EUnit :@ ())
evaluateTopLevel' (RPair (RSymbol "begin" :# _) r :# _) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel rs'
        pure $ last xs
      Nothing -> throwError (BadBegin r)
    Nothing -> throwError (BadBegin r)
evaluateTopLevel' e = evaluateRaw Nothing e

evaluateTopLevel ::
  (Monoid l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
  Raw l ->
  m (Typed ())
evaluateTopLevel r = do
  env <- _environment <$> get
  r' <- runReaderT (macroExpand r) env
  evaluateTopLevel' r'
