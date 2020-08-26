{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator
  ( evaluate,
    evaluateType,
    evaluateTopLevel,
    analyzeUntyped,
  )
where

import qualified Data.Map as M
import Lens.Micro.Mtl ((%=))
import Relude.Extra.Map ((!?))
import Zaphod.Checker
import Zaphod.Types

data EvaluatorError
  = UndefinedVariable Symbol
  | UnanalyzedApply Typed
  | NotLambda Typed
  | ArgumentCount Int Int
  | InvalidParameters Raw
  | InvalidTuple Raw
  | UnexpectedUntyped Untyped
  deriving (Show)

instance Exception EvaluatorError

evaluate :: (MonadReader Environment m, MonadState CheckerState m) => Typed -> m Typed
evaluate x = do
  env <- ask
  runReaderT (eval x) env
  where
    eval (ESymbol s _) = do
      m <- (!? s) <$> ask
      case m of
        Just v -> pure v
        Nothing -> bug (UndefinedVariable s)
    eval (EAnnotation v z) = const z <<$>> eval v
    eval (EApply (ESymbol "if-nil" _) xs _) =
      case xs of
        [p, a, b] -> do
          p' <- eval p
          case p' of
            EUnit -> eval a
            _ -> eval b
        _ -> bug (ArgumentCount 3 (length xs))
    eval (EApply f xs _) = do
      f' <- eval f
      case f' of
        ELambda (Variable v) e env _ -> do
          xs' <- traverse eval xs
          local (\_ -> M.insert v (fromList' xs') env) $ eval e
        ELambda' vs e env _
          | length vs == length xs -> do
            vxs <- traverse (\(v, z) -> (v,) <$> eval z) $ zip vs xs
            local (\_ -> foldl' extend env vxs) $ eval e
          | otherwise -> bug (ArgumentCount (length vs) (length xs))
        ENative1 (Native1 g) _ ->
          case xs of
            [a] -> g <$> eval a
            _ -> bug (ArgumentCount 1 (length xs))
        ENative2 (Native2 g) _ ->
          case xs of
            [a, b] -> g <$> eval a <*> eval b
            _ -> bug (ArgumentCount 2 (length xs))
        _ -> bug (NotLambda f)
    eval p@(EPair _ _ _) = bug (UnanalyzedApply p)
    eval (ELambda v e _ t) = ELambda v e <$> ask <*> pure t
    eval (ELambda' vs e _ t) = ELambda' vs e <$> ask <*> pure t
    eval (EQuote z _) = pure z
    eval (EType t) = EType <$> evalType t
    eval e = pure e
    --
    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (M.insert s (EType $ ZUniversal u)) (evalType z)
    evalType (ZFunction a b) = ZFunction <$> evalType a <*> evalType b
    evalType (ZPair a b) = ZPair <$> evalType a <*> evalType b
    evalType (ZValue a) = unwrapType <$> eval a
    evalType (ZUntyped a) = bug (UnexpectedUntyped a)
    evalType z = pure z
    --
    extend env (Variable v, z) = M.insert v z env

evaluateType :: (MonadReader Environment m, MonadState CheckerState m) => Untyped -> m ZType
evaluateType u = do
  t <- check u (ZType 0)
  unwrapType <$> evaluate t

analyzeType :: (MonadReader Environment m, MonadState CheckerState m) => Raw -> m ZType
analyzeType RUnit = pure ZUnit
analyzeType x@(RSymbol _) = ZUntyped <$> analyzeUntyped x
analyzeType (RPair "forall" (RPair (RSymbol u) (RPair z RUnit))) =
  ZForall (Universal u) <$> analyzeType z
analyzeType (RPair "->" (RPair a (RPair b RUnit))) =
  ZFunction <$> analyzeType a <*> analyzeType b
analyzeType (RPair "tuple" ts) = unwrapType' <$> mkTuple ts
  where
    mkTuple RUnit = pure $ EType ZUnit
    mkTuple (RPair x xs) = do
      x' <- analyzeType x
      xs' <- mkTuple xs
      pure $ EApply "zcons" [EType x', xs'] ()
    mkTuple _ = bug (InvalidTuple ts)
analyzeType (RPair "quote" (RPair x RUnit)) =
  pure . ZUntyped $ EQuote (EType $ quoteType x) ()
  where
    quoteType :: Raw -> ZType
    quoteType RUnit = ZUnit
    quoteType (RPair l r) = ZPair (quoteType l) (quoteType r)
    quoteType (RSymbol s) = ZValue $ ESymbol s ZSymbol
analyzeType (RPair a b) =
  case maybeList b of
    Just xs ->
      let xs' = traverse (fmap EType . analyzeType) xs
       in ZUntyped <$> (EApply <$> analyzeUntyped a <*> xs' <*> pure ())
    Nothing -> ZPair <$> analyzeType a <*> analyzeType b

analyzeQuoted :: Raw -> Untyped
analyzeQuoted RUnit = EUnit
analyzeQuoted (RSymbol s) = ESymbol s ()
analyzeQuoted (RPair l r) = EPair (analyzeQuoted l) (analyzeQuoted r) ()

analyzeUntyped :: (MonadReader Environment m, MonadState CheckerState m) => Raw -> m Untyped
analyzeUntyped RUnit = pure EUnit
analyzeUntyped (RSymbol s) = pure $ ESymbol s ()
analyzeUntyped (RPair "lambda" (RPair (RSymbol x) (RPair e RUnit))) =
  ELambda (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure ()
analyzeUntyped (RPair "lambda" (RPair xs (RPair e RUnit))) =
  case mkParams xs of
    Just ps -> ELambda' ps <$> analyzeUntyped e <*> pure mempty <*> pure ()
    Nothing -> bug (InvalidParameters xs)
  where
    mkParams :: Raw -> Maybe [Variable]
    mkParams RUnit = Just []
    mkParams (RPair (RSymbol z) zs) = (Variable z :) <$> mkParams zs
    mkParams _ = Nothing
analyzeUntyped (RPair ":" (RPair e (RPair t RUnit))) = do
  t' <- analyzeType t
  EAnnotation <$> analyzeUntyped e <*> evaluateType (stripExpr t')
  where
    stripExpr (ZUntyped u) = u
    stripExpr z = EType z
analyzeUntyped (RPair "quote" (RPair x RUnit)) = pure $ EQuote (analyzeQuoted x) ()
analyzeUntyped (RPair "tuple" ts) = mkTuple ts
  where
    mkTuple RUnit = pure EUnit
    mkTuple (RPair e xs) = do
      e' <- analyzeUntyped e
      xs' <- mkTuple xs
      pure $ EApply "cons" [e', xs'] ()
    mkTuple _ = bug (InvalidTuple ts)
analyzeUntyped (RPair a b) =
  case maybeList b of
    Just xs -> EApply <$> analyzeUntyped a <*> (traverse analyzeUntyped xs) <*> pure ()
    Nothing -> EPair <$> analyzeUntyped a <*> analyzeUntyped b <*> pure ()

evaluateRaw :: (MonadState ZState m) => Raw -> m Typed
evaluateRaw e = do
  env <- _environment <$> get
  usingReaderT env $
    evaluatingStateT (emptyCheckerState env) (evaluate =<< synthesize =<< analyzeUntyped e)

evaluateTopLevel :: (MonadState ZState m) => Raw -> m Typed
evaluateTopLevel (RPair "def" (RPair (RSymbol s) (RPair e RUnit))) = do
  e' <- evaluateRaw e
  environment %= M.insert s e'
  pure EUnit
evaluateTopLevel e = evaluateRaw e
