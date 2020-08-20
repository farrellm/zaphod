{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator (evaluate, evaluateType) where

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
    eval (EApply (ESymbol "cons" _) [l, r] _) = do
      l' <- eval l
      r' <- eval r
      pure $ EPair l' r' (ZPair (exprType l') (exprType r'))
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
