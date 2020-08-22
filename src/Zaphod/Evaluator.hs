{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator (evaluate, evaluateType, analyzeUntyped) where

import qualified Data.Map as M
import Relude.Extra.Map ((!?))
import Zaphod.Checker
import Zaphod.Types

data EvaluatorError
  = UndefinedVariable Symbol
  | UnanalyzedApply Typed
  | NotLambda Typed
  | ArgumentCount Int Int
  | InvalidType Text
  | InvalidParameters Raw
  | UnexpectedUntyped Untyped
  deriving (Show)

instance Exception EvaluatorError

evaluate :: (MonadState ZState m) => Typed -> m Typed
evaluate x = do
  env <- _environment <$> get
  runReaderT (eval x) env
  where
    eval :: (MonadState ZState m, MonadReader Environment m) => Typed -> m Typed
    eval (ESymbol s _) = do
      m <- (!? s) <$> ask
      case m of
        Just v -> pure v
        Nothing -> bug (UndefinedVariable s)
    eval (EAnnotation v _) = pure v
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

evaluateType :: Untyped -> State ZState ZType
evaluateType u = do
  t <- check u (ZType 0)
  unwrapType <$> evaluate t

analyzeType :: Raw -> ZType
analyzeType RUnit = ZUnit
analyzeType (RSymbol x) = ZUntyped (ESymbol x ())
analyzeType (RPair "forall" (RPair (RSymbol u) (RPair z RUnit))) =
  ZForall (Universal u) (analyzeType z)
analyzeType (RPair "->" (RPair a (RPair b RUnit))) =
  ZFunction (analyzeType a) (analyzeType b)
analyzeType t =
  case maybeList t of
    Just ts -> fromList' (analyzeType <$> ts)
    Nothing -> bug (InvalidType $ render t)

analyzeQuoted :: Raw -> Untyped
analyzeQuoted RUnit = EUnit
analyzeQuoted (RSymbol s) = ESymbol s ()
analyzeQuoted (RPair l r) = EPair (analyzeQuoted l) (analyzeQuoted r) ()

analyzeUntyped :: Raw -> State ZState Untyped
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
  let t' = analyzeType t
  EAnnotation <$> analyzeUntyped e <*> evaluateType (EType t')
analyzeUntyped (RPair "quote" (RPair x RUnit)) = pure $ EQuote (analyzeQuoted x) ()
analyzeUntyped (RPair a b) =
  case maybeList b of
    Just xs -> EApply <$> analyzeUntyped a <*> (traverse analyzeUntyped xs) <*> pure ()
    Nothing -> EPair <$> analyzeUntyped a <*> analyzeUntyped b <*> pure ()
