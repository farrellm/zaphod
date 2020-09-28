{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Zaphod.Evaluator
  ( evaluate,
    evaluateType,
    evaluateTopLevel,
    analyzeUntyped,
    macroExpand,
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
  | UnanalyzedApply (Typed ())
  | NotLambda (Typed ())
  | ArgumentCount Int Int
  | InvalidParameters (Raw ())
  | UnexpectedUntyped (Untyped ())
  | MissingExistential Existential
  | BadRaw (Typed ())
  | BadBegin (Raw ())
  | Impossible
  | NoMatches ZType
  | MultipleMatches ZType [Typed ()]
  deriving (Show)

instance Exception EvaluatorError

setType :: ZType -> Typed l -> Typed l
setType _ (EUnit l) = EUnit l
setType _ (EType z l) = EType z l
setType z (ESymbol s _ l) = ESymbol s z l
setType z (ELambda x e env _ l) = ELambda x e env z l
setType z (ELambda' xs e env _ l) = ELambda' xs e env z l
setType z (EImplicit x e env _ l) = EImplicit x e env z l
setType z (EMacro x e _ l) = EMacro x e z l
setType z (EMacro' x e _ l) = EMacro' x e z l
setType z (EApply f xs _ l) = EApply f xs z l
setType z (EPair l r _ loc) = EPair l r z loc
setType z (EAnnotation e _ l) = EAnnotation e z l
setType z (EQuote q _ l) = EQuote q z l
setType z (ENative1 n _ l) = ENative1 n z l
setType z (ENative2 n _ l) = ENative2 n z l
setType z (ENativeIO n _ l) = ENativeIO n z l
setType z (ESpecial _ l) = ESpecial z l

evaluate ::
  (MonadReader Environment m, MonadIO m) =>
  Typed l ->
  m (Typed ())
evaluate x = do
  env <- ask
  runReaderT (eval x) (mempty, env)
  where
    eval ::
      (MonadReader Environment m, MonadIO m) =>
      Typed l ->
      ReaderT (Map Symbol (Typed ()), Map Symbol (Typed ())) m (Typed ())
    eval (ESymbol s _ _) = do
      (m, n) <- bimap (!? s) (!? s) <$> ask
      pure $ case (m, n) of
        (Just v, _) -> v
        (_, Just v) -> v
        (_, _) -> bug (UndefinedVariable s)
    eval (EAnnotation v z _) = setType z <$> eval v
    eval (EApply (ESymbol "if" _ _) xs _ _) =
      case xs of
        [p, a, b] -> do
          p' <- eval p
          if p' == zTrue
            then eval a
            else eval b
        _ -> bug (ArgumentCount 3 (length xs))
    eval (EApply (ESymbol "apply" _ _) [f, xs] r _) = do
      f' <- eval f
      xs' <- eval xs
      setType r <$> case (f', maybeList xs') of
        (ELambda (Variable v) e env _ _, _) -> do
          local (\(_, n) -> (M.insert v xs' env, n)) $ eval e
        (EImplicit (Variable v) e env _ _, _) -> do
          local (\(_, n) -> (M.insert v xs' env, n)) $ eval e
        (ELambda' vs e env _ _, Just ys) -> do
          let vxs = zip vs ys
          local (\(_, n) -> (foldl' extend env vxs, n)) $ eval e
        (ENative1 (Native1 g) _ _, Just [a]) ->
          pure $ g a
        (ENative2 (Native2 g) _ _, Just [a, b]) ->
          pure $ g a b
        _ -> bug Impossible
    eval (EApply f xs r _) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda (Variable v) e env _ _ -> do
          xs' <- traverse eval xs
          local (\(_, n) -> (M.insert v (fromList xs') env, n)) $ eval e
        ELambda' vs e env _ _
          | length vs == length xs -> do
            vxs <- traverse (\(v, z) -> (v,) <$> eval z) $ zip vs xs
            local (\(_, n) -> (foldl' extend env vxs, n)) $ eval e
          | otherwise -> bug (ArgumentCount (length vs) (length xs))
        EImplicit (Variable v) e env (ZFunction i _) _ -> do
          (a, b) <- bimap (findOfType i) (findOfType i) <$> ask
          case (M.toList a ++ M.toList b) of
            [(_, s)] -> local (\(_, n) -> (M.insert v s env, n)) $ eval e
            [] -> bug $ NoMatches i
            ss -> bug $ MultipleMatches i (snd <$> ss)
        ENative1 (Native1 g) _ _ ->
          case xs of
            [a] -> g <$> eval a
            _ -> bug (ArgumentCount 1 (length xs))
        ENative2 (Native2 g) _ _ ->
          case xs of
            [a, b] -> g <$> eval a <*> eval b
            _ -> bug (ArgumentCount 2 (length xs))
        ENativeIO (NativeIO g) _ _ ->
          case xs of
            [] -> liftIO g
            _ -> bug (ArgumentCount 0 (length xs))
        _ -> bug (NotLambda $ stripLocation f)
      where
        findOfType z = M.filter ((z ==) . exprType)
    eval p@(EPair _ _ _ _) = bug (UnanalyzedApply $ stripLocation p)
    eval (ELambda v e _ t _) = ELambda v (stripLocation e) <$> (fst <$> ask) <*> pure t <*> pure ()
    eval (ELambda' vs e _ t _) = ELambda' vs (stripLocation e) <$> (fst <$> ask) <*> pure t <*> pure ()
    eval (EQuote z _ _) = pure (stripLocation z)
    eval (EType t _) = EType <$> evalType t <*> pure ()
    eval e = pure (stripLocation e)
    --
    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (first (M.insert s (EType (ZUniversal u) ()))) (evalType z)
    evalType (ZFunction a b) = ZFunction <$> evalType a <*> evalType b
    evalType (ZPair a b) = ZPair <$> evalType a <*> evalType b
    evalType (ZValue a) = unwrapType <$> eval a
    evalType (ZUntyped a) = bug (UnexpectedUntyped a)
    evalType z = pure z
    --
    extend env (Variable v, z) = M.insert v z env

evaluateType ::
  (Monoid l, MonadReader Environment m, MonadIO m) =>
  (Untyped l) ->
  m ZType
evaluateType u = do
  env <- ask
  t <- evaluatingStateT (emptyCheckerState env) $ check u (ZType 0)
  unwrapType <$> evaluate t

analyzeType ::
  (Monoid l, MonadReader Environment m, MonadIO m) =>
  Raw l ->
  m ZType
analyzeType (RUnit _) = pure ZUnit
analyzeType x@(RSymbol _ _) = ZUntyped . stripLocation <$> analyzeUntyped x
analyzeType (RPair (RSymbol "forall" _) (RPair (RSymbol u _) (RPair z (RUnit _) _) _) _) =
  ZForall (Universal u) <$> analyzeType z
analyzeType (RPair (RSymbol "->" _) (RPair a (RPair b (RUnit _) _) _) _) =
  ZFunction <$> analyzeType a <*> analyzeType b
analyzeType (RPair (RSymbol "quote" _) (RPair x (RUnit _) _) _) =
  pure . ZUntyped $ EQuote (EType (quoteType x) ()) () ()
  where
    quoteType :: Raw l -> ZType
    quoteType (RUnit _) = ZUnit
    quoteType (RPair l r _) = ZPair (quoteType l) (quoteType r)
    quoteType (RSymbol s _) = ZValue $ ESymbol s ZSymbol ()
analyzeType (RPair (RSymbol "cons" _) ts _) = analyzeType (RPair "zcons" ts mempty)
analyzeType (RPair a b _) =
  case maybeList b of
    Just xs -> do
      xs' <- traverse (fmap (\z -> EType z ()) . analyzeType) xs
      a' <- stripLocation <$> analyzeUntyped a
      pure $ ZUntyped (EApply a' xs' () ())
    Nothing -> ZPair <$> analyzeType a <*> analyzeType b

analyzeQuoted :: Raw l -> Untyped l
analyzeQuoted (RUnit l) = EUnit l
analyzeQuoted (RSymbol s l) = ESymbol s () l
analyzeQuoted (RPair l r loc) = EPair (analyzeQuoted l) (analyzeQuoted r) () loc

mkParams :: Raw l -> Maybe [Variable]
mkParams (RUnit _) = Just []
mkParams (RPair (RSymbol z _) zs _) = (Variable z :) <$> mkParams zs
mkParams _ = Nothing

analyzeUntyped ::
  (Monoid l, MonadReader Environment m, MonadIO m) =>
  Raw l ->
  m (Untyped l)
analyzeUntyped (RUnit l) = pure (EUnit l)
analyzeUntyped (RSymbol s l) = pure $ ESymbol s () l
analyzeUntyped (RPair (RSymbol "lambda" _) (RPair (RSymbol x _) (RPair e (RUnit _) _) _) l) =
  ELambda (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure () <*> pure l
analyzeUntyped (RPair (RSymbol "lambda" _) (RPair xs (RPair e (RUnit _) _) _) l) =
  case mkParams xs of
    Just ps -> ELambda' ps <$> analyzeUntyped e <*> pure mempty <*> pure () <*> pure l
    Nothing -> bug (InvalidParameters $ stripLocation xs)
analyzeUntyped (RPair (RSymbol "implicit" _) (RPair (RSymbol x _) (RPair e (RUnit _) _) _) l) =
  EImplicit (Variable x) <$> analyzeUntyped e <*> pure mempty <*> pure () <*> pure l
analyzeUntyped (RPair (RSymbol "macro" _) (RPair (RSymbol x _) (RPair e (RUnit _) _) _) l) =
  EMacro (Variable x) <$> analyzeUntyped e <*> pure () <*> pure l
analyzeUntyped (RPair (RSymbol "macro" _) (RPair xs (RPair e (RUnit _) _) _) l) =
  case mkParams xs of
    Just ps -> EMacro' ps <$> analyzeUntyped e <*> pure () <*> pure l
    Nothing -> bug (InvalidParameters $ stripLocation xs)
analyzeUntyped (RPair (RSymbol ":" _) (RPair t (RPair (RSymbol "Type" _) (RUnit _) _) _) l) = do
  EType <$> analyzeType t <*> pure l
analyzeUntyped (RPair (RSymbol ":" _) (RPair e (RPair t (RUnit _) _) _) l) = do
  EAnnotation <$> analyzeUntyped e <*> evaluateRawType t <*> pure l
analyzeUntyped (RPair (RSymbol "quote" _) (RPair x (RUnit _) _) l) = pure $ EQuote (analyzeQuoted x) () l
analyzeUntyped (RPair a b l) =
  case maybeList b of
    Just xs -> EApply <$> analyzeUntyped a <*> traverse analyzeUntyped xs <*> pure () <*> pure l
    Nothing -> EPair <$> analyzeUntyped a <*> analyzeUntyped b <*> pure () <*> pure l

evaluateRaw ::
  (Monoid l, MonadState ZState m, MonadIO m) =>
  Maybe (Symbol, Raw l) ->
  Raw l ->
  m (Typed ())
evaluateRaw m x = do
  env <- _environment <$> get
  x' <-
    usingReaderT env
      . evaluatingStateT (emptyCheckerState env)
      $ do
        case m of
          Just (n, (RSymbol "Type" _)) -> do
            context %= (CVariable (Variable n) (ZType 0) <:)
            EType <$> evaluateRawType x <*> pure ()
          Just (n, t) -> do
            t' <- evaluateRawType t
            context %= (CVariable (Variable n) t' <:)
            let x' = (RPair ":" (RPair x (RPair t (RUnit mempty) mempty) mempty) mempty)
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

evaluateRawType ::
  (Monoid l, MonadReader Environment m, MonadIO m) =>
  Raw l ->
  m ZType
evaluateRawType t = do
  t' <- analyzeType t
  evaluateType (stripExpr t')
  where
    stripExpr (ZUntyped u) = u
    stripExpr z = EType z ()

macroExpand1 :: (Monoid l, MonadReader Environment m, MonadIO m) => Raw l -> m (Raw l)
macroExpand1 w = do
  env <- ask
  evaluatingStateT (emptyCheckerState env) $ do
    go w
  where
    go q@(RPair a@(RSymbol s _) b lq) =
      case maybeList b of
        Just xs -> do
          f <- M.lookup s <$> ask
          case f of
            Just (EMacro v e _ ()) -> do
              let f' = setLocation mempty $ ELambda v (stripType e) mempty () ()
              xs' <- traverse (analyzeUntyped . quote) xs
              x' <- evaluate =<< synthesize (EApply f' xs' () lq)
              checkResult x' xs
            Just (EMacro' vs e _ ()) -> do
              let f' = setLocation mempty $ ELambda' vs (stripType e) mempty () ()
              xs' <- traverse (analyzeUntyped . quote) xs
              x' <- evaluate =<< synthesize (EApply f' xs' () lq)
              checkResult x' xs
            _ -> goList xs
        Nothing -> RPair a <$> go b <*> pure lq
      where
        q' = stripLocation q

        checkResult x' xs = do
          let r = toRaw x'
          if r /= q'
            then pure $ setLocation lq r
            else goList xs

        goList xs = fromList . (a :) <$> traverse go xs
    go (RPair l r lp) = RPair <$> go l <*> go r <*> pure lp
    go r = pure r

    quote e = RPair "quote" (RPair e (RUnit mempty) mempty) mempty

    toRaw (EUnit l) = RUnit l
    toRaw (ESymbol s _ l) = RSymbol s l
    toRaw (EPair l r _ lp) = RPair (toRaw l) (toRaw r) lp
    toRaw e = bug $ BadRaw e

macroExpand :: (Monoid l, MonadReader Environment m, MonadIO m) => Raw l -> m (Raw l)
macroExpand w = do
  w' <- macroExpand1 w
  if stripLocation w == stripLocation w'
    then pure w
    else macroExpand w'

evaluateTopLevel' :: (Monoid l, MonadState ZState m, MonadIO m) => Raw l -> m (Typed ())
evaluateTopLevel' (RPair (RSymbol "def" _) (RPair (RSymbol s _) (RPair e (RUnit _) _) _) _) = do
  e' <- evaluateRaw Nothing e
  environment %= M.insert s e'
  pure (EUnit ())
evaluateTopLevel' (RPair (RSymbol "def" _) (RPair (RSymbol s _) (RPair t (RPair e (RUnit _) _) _) _) _) = do
  e' <- evaluateRaw (Just (s, t)) e
  environment %= M.insert s e'
  pure (EUnit ())
evaluateTopLevel' (RPair (RSymbol "begin" _) r _) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel rs'
        pure $ last xs
      Nothing -> bug $ BadBegin (stripLocation r)
    Nothing -> bug $ BadBegin (stripLocation r)
evaluateTopLevel' e = do
  evaluateRaw Nothing e

evaluateTopLevel :: (Monoid l, MonadState ZState m, MonadIO m) => Raw l -> m (Typed ())
evaluateTopLevel r = do
  env <- _environment <$> get
  r' <- runReaderT (macroExpand r) env
  evaluateTopLevel' r'
