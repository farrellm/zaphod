{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator (evaluate) where

import qualified Data.Map as M
import Relude.Extra.Map ((!?))
import Zaphod.Types

data EvaluatorError
  = UndefinedVariable Symbol
  | UnanalyzedApply Typed
  | NotLambda Typed
  | ArgumentCount Int Int
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
    eval (EApply (ELambda (Variable v) e _) xs _) = do
      xs' <- traverse eval xs
      local (M.insert v (makeTypedList xs')) $ eval e
    eval (EApply (ELambda' vs e _) xs _)
      | length vs == length xs = do
        vxs <- traverse (\(v, z) -> (v,) <$> eval z) $ zip vs xs
        local (\env -> foldl' extend env vxs) $ eval e
      | otherwise = bug (ArgumentCount (length vs) (length xs))
    eval (EApply f _ _) = bug (NotLambda f)
    eval p@(EPair _ _ _) = bug (UnanalyzedApply p)
    eval e = pure e
    --
    extend env (Variable v, z) = M.insert v z env
