{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  ( Semigroup l,
    Location l,
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

isSubtype ::
  (MonadReader Environment m, MonadError (EvaluatorException ()) m) =>
  ZType ->
  ZType ->
  m Bool
isSubtype a b = do
  env <- ask
  e <- runExceptT (evaluatingStateT (emptyCheckerState env) $ subtype a b)
  case e of
    Right () -> pure True
    Left NotSubtype {} -> pure False
    Left err -> throwError (CheckerException err)

evaluate :: (MonadEvaluator l m) => Typed l -> m (Typed ())
evaluate expr = do
  env <- ask
  runReaderT (eval expr) (mempty, env)
  where
    eval ::
      ( Semigroup k,
        Location k,
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
    eval (EApplyN (ESymbol "if" _ :@ _) xs _ :@ _) =
      case xs of
        [p, a, b] -> do
          p' <- eval p
          if p' == zTrue
            then eval a
            else eval b
        _ -> bug Unreachable
    eval (EApplyN (ESymbol "apply" _ :@ _) [f, xs] r :@ l) = eval (EApply1 f xs r :@ l)
    eval (EApply1 f x r :@ l) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda1 (Variable v) e env _ :@ _ -> do
          x' <- eval x
          local (\(_, n) -> (M.insert v x' env, n)) . errorLocation l $ eval e
        ELambdaN vs e env _ :@ _ -> do
          mxs' <- eval x
          case nonEmpty <$> maybeList mxs' of
            Just (Just xs') ->
              local (\(_, n) -> (foldl' insertVar env (zip vs $ toList xs'), n))
                . errorLocation l
                $ eval e
            Just Nothing -> errorLocation l $ eval e
            Nothing -> bug Unreachable
        EImplicit (Variable v) e env (ZImplicit i _) :@ _ -> do
          (lcl, gbl) <- ask
          a <- errorLocation l $ findOfType i lcl
          b <- errorLocation l $ findOfType i gbl
          case M.toList a ++ M.toList b of
            [(_, s)] ->
              local (\(_, n) -> (M.insert v s env, n)) $
                eval (EApply1 (setLocation (location f) e) x r :@ l)
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
        ENativeIO (NativeIO g) _ :@ _ -> liftIO g
        _ -> bug Unreachable
    eval (EApplyN f xs r :@ l) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda1 (Variable v) e env _ :@ _ -> do
          x' <- eval (fromNonEmpty xs)
          local (\(_, n) -> (M.insert v x' env, n)) . errorLocation l $ eval e
        ELambdaN vs e env _ :@ _ -> do
          xs' <- traverse eval xs
          local (\(_, n) -> (foldl' insertVar env (zip vs $ toList xs'), n))
            . errorLocation l
            $ eval e
        EImplicit (Variable v) e env (ZImplicit i _) :@ _ -> do
          (lcl, gbl) <- ask
          a <- errorLocation l $ findOfType i lcl
          b <- errorLocation l $ findOfType i gbl
          case M.toList a ++ M.toList b of
            [(_, s)] ->
              local (\(_, n) -> (M.insert v s env, n)) $
                eval (EApplyN (setLocation (location f) e) xs r :@ l)
            [] -> throwError (NoMatches i)
            ss -> throwError (MultipleMatches i (snd <$> ss))
        ENative1 (Native1 g) _ :@ _ ->
          case xs of
            [x] -> do
              x' <- eval x
              errorLocation l . liftNative $ g x'
            _ -> bug Unreachable
        ENative2 (Native2 g) _ :@ _ ->
          case xs of
            [a, b] -> do
              a' <- eval a
              b' <- eval b
              errorLocation l . liftNative $ g a' b'
            _ -> bug Unreachable
        ENativeIO (NativeIO g) _ :@ _ -> liftIO g
        _ -> bug Unreachable
    eval (EPair a b t :@ _) = (:@ ()) <$> (EPair <$> eval a <*> eval b <*> pure t)
    eval (ELambda1 v e _ t :@ _) = (:@ ()) <$> (ELambda1 v (stripLocation e) <$> (fst <$> ask) <*> pure t)
    eval (ELambdaN vs e _ t :@ _) = (:@ ()) <$> (ELambdaN vs (stripLocation e) <$> (fst <$> ask) <*> pure t)
    eval (EQuote z _ :@ _) = pure (stripLocation z)
    eval (EType t :@ l) = (:@ ()) . EType <$> errorLocation l (evalType t)
    eval e = pure (stripLocation e)

    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (first (M.insert s (EType (ZUniversal u) :@ ()))) (evalType z)
    evalType (ZFunction a b) = ZFunction <$> evalType a <*> evalType b
    evalType (ZImplicit a b) = ZImplicit <$> evalType a <*> evalType b
    evalType (ZPair a b) = ZPair <$> evalType a <*> evalType b
    evalType (ZValue a) = unwrapType <$> eval a
    evalType (ZUntyped _) = bug Unreachable
    evalType z = pure z

    findOfType z env = do
      (lcl, gbl) <- ask
      usingReaderT (M.union lcl gbl) $
        M.fromList <$> filterM (isSubtype z . exprType . snd) (M.toList env)

    insertVar env (Variable v, x) = M.insert v x env

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
  case nonEmpty <$> maybeList b of
    Just (Just xs) -> do
      xs' <- traverse (fmap unwrapUntyped . analyzeType) xs
      pure $ ZUntyped (EApplyN a' xs' () :@ ())
    Just Nothing -> pure $ ZUntyped (EApply1 a' (EUnit :@ ()) () :@ ())
    Nothing -> do
      b' <- analyzeType b
      pure $ ZUntyped (EApply1 a' (EType b' :@ ()) () :@ ())

analyzeQuoted :: Raw l -> Untyped l
analyzeQuoted (RUnit :# l) = EUnit :@ l
analyzeQuoted (RSymbol s :# l) = ESymbol s () :@ l
analyzeQuoted (RPair x y :# l) = EPair (analyzeQuoted x) (analyzeQuoted y) () :@ l

analyzeUntyped :: (MonadEvaluator l m) => Raw l -> m (Untyped l)
analyzeUntyped (RUnit :# l) = pure (EUnit :@ l)
analyzeUntyped (RSymbol s :# l) = pure $ ESymbol s () :@ l
analyzeUntyped (RS "lambda" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (ELambda1 (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure ())
analyzeUntyped (RS "lambda" `RPair` (mxs :. e :. RU) :# l)
  | Just xs <- maybeList mxs,
    Just vs <- traverse maybeSymbol xs =
    (:@ l) <$> (ELambdaN (Variable <$> vs) <$> analyzeUntyped e <*> pure mempty <*> pure ())
analyzeUntyped r@(RS "lambda" `RPair` _ :# _) = throwError (InvalidLambda r)
analyzeUntyped (RS "implicit" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (EImplicit (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure ())
analyzeUntyped (RS "macro" `RPair` (RS x :. e :. RU) :# l) =
  (:@ l) <$> (EMacro1 (Variable x) <$> analyzeUntyped e <*> pure ())
analyzeUntyped (RS "macro" `RPair` (mxs :. e :. RU) :# l)
  | Just xs <- maybeList mxs,
    Just vs <- traverse maybeSymbol xs =
    (:@ l) <$> (EMacroN (Variable <$> vs) <$> analyzeUntyped e <*> pure ())
analyzeUntyped r@(RS "macro" `RPair` _ :# _) = throwError (InvalidMacro r)
analyzeUntyped (RS ":" `RPair` (t :. RS "Type" :. RU) :# l) =
  (:@ l) . EType <$> analyzeType t
analyzeUntyped (RS ":" `RPair` (e :. t :. RU) :# l) =
  (:@ l) <$> (EAnnotation <$> analyzeUntyped e <*> evaluateRawType t)
analyzeUntyped (RS "quote" `RPair` (x :. RU) :# l) =
  pure $ EQuote (analyzeQuoted x) () :@ l
analyzeUntyped (RPair a b :# l) =
  case nonEmpty <$> maybeList b of
    Just (Just xs) ->
      (:@ l) <$> (EApplyN <$> analyzeUntyped a <*> traverse analyzeUntyped xs <*> pure ())
    Just Nothing ->
      (:@ l) <$> (EApply1 <$> analyzeUntyped a <*> pure (EUnit :@ getEnd l) <*> pure ())
    Nothing -> (:@ l) <$> (EApply1 <$> analyzeUntyped a <*> analyzeUntyped b <*> pure ())

maybeSymbol :: Raw l -> Maybe Symbol
maybeSymbol (RSymbol s :# _) = Just s
maybeSymbol _ = Nothing

evaluateRaw ::
  (Semigroup l, Location l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
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
          r <- evaluate =<< liftChecker (`check` t') =<< analyzeUntyped x
          pure $ setType t' r
        Nothing -> evaluate =<< liftChecker synthesize =<< analyzeUntyped x
  pure (first universalize x')
  where
    universalize z =
      let es = unbound z
          us = universals z
          eus = mkEUMap (S.toList es) us ['a' ..]
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
        Just (EMacro1 v e _ :@ ()) -> goMacro $ ELambda1 v (stripType e) mempty () :@ ()
        Just (EMacroN vs e _ :@ ()) -> goMacro $ ELambdaN vs (stripType e) mempty () :@ ()
        _ -> (:# lq) . RPair a <$> goInner b
      where
        goMacro l = do
          let f' = setLocation lq l
          b' <- analyzeUntyped $ quote b
          x' <- evaluate =<< liftChecker synthesize (EApply1 f' b' () :@ lq)
          pure $ setLocation lq (toRaw x')
    go (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    go r = pure r

    goInner (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    goInner r = pure r

    quote e@(_ :# l) = (RSymbol "quote" :# getBegin l) <> (e <> (RUnit :# getEnd l))

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
  (Semigroup l, Location l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
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
  (Semigroup l, Location l, MonadState ZState m, MonadError (EvaluatorException l) m, MonadIO m) =>
  Raw l ->
  m (Typed ())
evaluateTopLevel r = do
  env <- _environment <$> get
  r' <- runReaderT (macroExpand r) env
  evaluateTopLevel' r'
