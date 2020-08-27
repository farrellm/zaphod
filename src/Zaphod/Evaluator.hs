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
import qualified Data.Set as S
import Lens.Micro.Mtl ((%=))
import Relude.Extra.Map ((!?))
import Zaphod.Base
import Zaphod.Checker
import Zaphod.Context
import Zaphod.Types

data EvaluatorError
  = UndefinedVariable Symbol
  | UnanalyzedApply Typed
  | NotLambda Typed
  | ArgumentCount Int Int
  | InvalidParameters Raw
  | InvalidTuple Raw
  | UnexpectedUntyped Untyped
  | MissingExistential Existential
  | Impossible
  deriving (Show)

instance Exception EvaluatorError

setType :: ZType -> Typed -> Typed
setType _ EUnit = EUnit
setType _ z@(EType _) = z
setType z (ESymbol s _) = ESymbol s z
setType z (ELambda x e env _) = ELambda x e env z
setType z (ELambda' xs e env _) = ELambda' xs e env z
setType z (EApply f xs _) = EApply f xs z
setType z (EPair l r _) = EPair l r z
setType z (EAnnotation e _) = EAnnotation e z
setType z (EQuote q _) = EQuote q z
setType z (ENative1 n _) = ENative1 n z
setType z (ENative2 n _) = ENative2 n z
setType z (ESpecial _) = ESpecial z

evaluate :: (MonadReader Environment m, MonadState CheckerState m) => Typed -> m Typed
evaluate x = do
  env <- ask
  runReaderT (eval x) (mempty, env)
  where
    eval (ESymbol s _) = do
      (m, n) <- bimap (!? s) (!? s) <$> ask
      case (m, n) of
        (Just v, _) -> pure v
        (_, Just v) -> pure v
        (_, _) -> bug (UndefinedVariable s)
    eval (EAnnotation v z) = setType z <$> eval v
    eval (EApply (ESymbol "if" _) xs _) =
      case xs of
        [p, a, b] -> do
          p' <- eval p
          if p' == zTrue
            then eval a
            else eval b
        _ -> bug (ArgumentCount 3 (length xs))
    eval (EApply f xs r) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda (Variable v) e env _ -> do
          xs' <- traverse eval xs
          local (\(_, n) -> (M.insert v (fromList' xs') env, n)) $ eval e
        ELambda' vs e env _
          | length vs == length xs -> do
            vxs <- traverse (\(v, z) -> (v,) <$> eval z) $ zip vs xs
            local (\(_, n) -> (foldl' extend env vxs, n)) $ eval e
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
    eval (ELambda v e _ t) = ELambda v e <$> (fst <$> ask) <*> pure t
    eval (ELambda' vs e _ t) = ELambda' vs e <$> (fst <$> ask) <*> pure t
    eval (EQuote z _) = pure z
    eval (EType t) = EType <$> evalType t
    eval e = pure e
    --
    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (first (M.insert s (EType $ ZUniversal u))) (evalType z)
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
analyzeUntyped (RPair ":" (RPair t (RPair "Type" RUnit))) = do
  EType <$> analyzeType t
analyzeUntyped (RPair ":" (RPair e (RPair t RUnit))) = do
  EAnnotation <$> analyzeUntyped e <*> evaluateRawType t
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

evaluateRaw :: (MonadState ZState m) => Maybe (Symbol, Raw) -> Raw -> m Typed
evaluateRaw m x = do
  env <- _environment <$> get
  x' <-
    usingReaderT env
      . evaluatingStateT (emptyCheckerState env)
      $ do
        case m of
          Just (n, "Type") -> do
            context %= (CVariable (Variable n) (ZType 0) <:)
            EType <$> evaluateRawType x
          Just (n, t) -> do
            t' <- evaluateRawType t
            context %= (CVariable (Variable n) t' <:)
            let x' = (RPair ":" (RPair x (RPair t RUnit)))
            evaluate =<< synthesize =<< analyzeUntyped x'
          Nothing -> evaluate =<< synthesize =<< analyzeUntyped x
  pure (universalize <$> x')
  where
    universalize z =
      let es = unbound z
          us = universals z
          eus = mkEUMap (toList es) us ['a' ..]
       in foldl' (flip ZForall) (replaceExt eus z) eus

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
    mkEUMap _ _ [] = bug Impossible

    replaceExt eus (ZExistential e) = case M.lookup e eus of
      Just u -> ZUniversal u
      Nothing -> bug $ MissingExistential e
    replaceExt eus (ZForall u z) = ZForall u $ replaceExt eus z
    replaceExt eus (ZFunction a b) = ZFunction (replaceExt eus a) (replaceExt eus b)
    replaceExt eus (ZPair a b) = ZPair (replaceExt eus a) (replaceExt eus b)
    replaceExt eus (ZValue a) = ZValue $ setType (replaceExt eus $ exprType a) a
    replaceExt _ z = z

evaluateRawType :: (MonadReader Environment m, MonadState CheckerState m) => Raw -> m ZType
evaluateRawType t = do
  t' <- analyzeType t
  evaluateType (stripExpr t')
  where
    stripExpr (ZUntyped u) = u
    stripExpr z = EType z

evaluateTopLevel :: (MonadState ZState m) => Raw -> m Typed
evaluateTopLevel (RPair "def" (RPair (RSymbol s) (RPair e RUnit))) = do
  e' <- evaluateRaw Nothing e
  environment %= M.insert s e'
  pure EUnit
evaluateTopLevel (RPair "def" (RPair (RSymbol s) (RPair t (RPair e RUnit)))) = do
  e' <- evaluateRaw (Just (s, t)) e
  environment %= M.insert s e'
  pure EUnit
evaluateTopLevel e = evaluateRaw Nothing e
