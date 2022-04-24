{-# LANGUAGE OverloadedStrings #-}

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
import Lens.Micro.Platform (at, to, view, (%=), (%~), (.~), (?=), (?~))
import Relude.Extra.Map (elems, insert)
import Zaphod.Base (zTrue)
import Zaphod.Checker (check, isSubtype, synthesize)
import Zaphod.Context ((<:))
import Zaphod.Types

unwrapType :: Typed l -> ZType (Typed l)
unwrapType ((EType z) :@ _) = z
unwrapType _ = bug Unreachable

liftChecker ::
  (MonadEvaluator l m) =>
  [(Symbol, ZType (Typed l))] ->
  ExceptT (CheckerException l) (StateT (CheckerState l) m) b ->
  m b
liftChecker bs x = do
  env <- view environment
  e <- evaluatingStateT (emptyCheckerState env) $ do
    for_ bs $ \(n, t) ->
      context %= (CVariable (Variable n) t <:)
    runExceptT x
  case e of
    Right res -> pure res
    Left err -> throwError (CheckerException err)

liftNative :: (MonadError (EvaluatorException l) m) => l -> Either (NativeException ()) a -> m a
liftNative l = liftEither . first (NativeException . fmap (const l))

findOfType :: (MonadEvaluator l m) => l -> ZType (Typed l) -> m (Typed l)
findOfType l z = do
  vs <- view (environment . to elems)
  xs <- liftChecker [] $ filterM (isSubtype z . exprType) vs
  case xs of
    [x] -> pure x
    [] -> throwError (NoMatches (project z) l)
    _ -> throwError (MultipleMatches (project z) (project <$> xs) l)

infer :: (MonadEvaluator l m) => Typed l -> m (Typed l)
infer (EApplyN f@(_ :@ (l, ZImplicit a b)) xs :@ lt) = do
  i <- findOfType l a
  e <- infer (EApply1 f i :@ (l, b))
  pure (EApplyN e xs :@ lt)
infer (ELambda1 v e env :@ lt) = (:@ lt) <$> (ELambda1 v <$> infer e <*> pure env)
infer (ELambdaN vs e env :@ lt) = (:@ lt) <$> (ELambdaN vs <$> infer e <*> pure env)
infer (EImplicit v@(Variable s) e :@ lt@(l, ZImplicit a _)) = do
  e' <- local (environment %~ insert s (ESymbol s :@ (l, a))) $ infer e
  pure (EImplicit v e' :@ lt)
infer (EApply1 f e :@ lt) = (:@ lt) <$> (EApply1 <$> infer f <*> infer e)
infer (EApplyN f es :@ lt) = (:@ lt) <$> (EApplyN <$> infer f <*> traverse infer es)
infer (EPair a b :@ lt) = (:@ lt) <$> (EPair <$> infer a <*> infer b)
infer (EAnnotation a z :@ lt) = (:@ lt) <$> (EAnnotation <$> infer a <*> pure z)
infer x = pure x

evaluate :: forall l m. (MonadEvaluator l m) => Typed l -> m (Typed l)
evaluate = eval
  where
    eval :: Typed l -> m (Typed l)
    eval (ESymbol s :@ (_, z)) = do
      m <- view (environment . at s)
      case m of
        Just v -> pure $ setType z v
        _ -> bug Unreachable
    eval (EAnnotation v z :@ _) = setType z <$> eval v
    eval (EApplyN o xs :@ lt)
      | ESymbol "if" :@ _ <- o =
        case xs of
          [p, a, b] -> do
            p' <- eval p
            if project p' == zTrue
              then eval a
              else eval b
          _ -> bug Unreachable
      | ESymbol "apply" :@ _ <- o,
        [f, xs'] <- xs =
        eval (EApply1 f xs' :@ lt)
    eval (EApply1 f x :@ (l, t)) = evalApply1 f x l t
    eval (EApplyN f xs :@ (l, t)) = evalApplyN f xs l t
    eval (EPair a b :@ lt) = (:@ lt) <$> (EPair <$> eval a <*> eval b)
    eval (ELambda1 v e _ :@ lt) = (:@ lt) <$> (ELambda1 v e <$> view environment)
    eval (ELambdaN vs e _ :@ lt) = (:@ lt) <$> (ELambdaN vs e <$> view environment)
    eval (EMacro1 v e _ :@ lt) = (:@ lt) <$> (EMacro1 v e <$> view environment)
    eval (EMacroN vs e _ :@ lt) = (:@ lt) <$> (EMacroN vs e <$> view environment)
    eval (EQuote z :@ _) = pure z
    eval (EQuasiQuote q :@ _) = evalQQ q
    eval (EType t :@ l) = (:@ l) . EType <$> evaluateType t
    eval e = pure e

    evalApply1 f x l t = do
      f' <- eval f
      x' <- eval x
      modifyError (CallSite l) $
        setType t <$> case f' of
          ELambda1 (Variable v) e env :@ _ ->
            local (environment .~ insert v x' env) $ eval e
          ELambdaN vs e env :@ _ ->
            case maybeList x' of
              Just xs' ->
                local (environment .~ foldl' insertVar env (zip vs xs')) $
                  eval e
              Nothing -> bug Unreachable
          EMacro1 (Variable v) e env :@ _ ->
            local (environment .~ insert v x' env) $ eval e
          EMacroN vs e env :@ _ ->
            case maybeList x' of
              Just xs' ->
                local (environment .~ foldl' insertVar env (zip vs xs')) $
                  eval e
              Nothing -> bug Unreachable
          EImplicit (Variable v) e :@ _ ->
            local (environment %~ insert v x') $ eval e
          ENative (Native g) :@ _ ->
            case maybeList x' of
              Just [a] -> liftNative l $ setLocation l <$> g (project a)
              _ -> bug Unreachable
          ENative' (Native' g) :@ _ ->
            case maybeList x' of
              Just [a] -> liftNative l $ g a
              _ -> bug Unreachable
          ENativeIO (NativeIO g) :@ _ -> setLocation l <$> liftIO g
          _ -> bug Unreachable

    evalApplyN f xs l t = do
      f' <- eval f
      xs' <- traverse eval xs
      modifyError (CallSite l) $
        setType t <$> case f' of
          ELambda1 (Variable v) e env :@ _ ->
            local (environment .~ insert v (typedTuple xs') env) $ eval e
          ELambdaN vs e env :@ _ ->
            local (environment .~ foldl' insertVar env (zip vs xs')) $ eval e
          EMacro1 (Variable v) e env :@ _ ->
            local (environment .~ insert v (typedTuple xs') env) $ eval e
          EMacroN vs e env :@ _ ->
            local (environment .~ foldl' insertVar env (zip vs xs')) $ eval e
          ENative (Native g) :@ _ ->
            case xs' of
              [x'] -> liftNative l $ setLocation l <$> g (project x')
              _ -> liftNative l $ setLocation l <$> g (project $ typedTuple xs')
          ENative' (Native' g) :@ _ ->
            case xs' of
              [x'] -> liftNative l $ g x'
              _ -> liftNative l $ g (typedTuple xs')
          ENativeIO (NativeIO g) :@ _ -> setLocation l <$> liftIO g
          _ -> debug (render f') $ bug Unreachable

    evalQQ e@(EUnit :@ _) = pure e
    evalQQ e@(ESymbol _ :@ _) = pure e
    evalQQ (EPair (EUnquoteSplicing q :@ _) r :@ _) =
      (<>) <$> eval q <*> evalQQ r
    evalQQ (EPair l r :@ lt) = (:@ lt) <$> (EPair <$> evalQQ l <*> evalQQ r)
    evalQQ (EUnquote e :@ _) = eval e
    evalQQ e = trace' (render e) $ bug Unreachable

    insertVar :: Environment a -> (Variable, a) -> Environment a
    insertVar env (Variable v, x) = insert v x env

evaluateType :: (MonadEvaluator l m) => ZType (Typed l) -> m (ZType (Typed l))
evaluateType (ZForall u@(Universal s) z) = do
  let u' = EType (ZUniversal u) :@ (mempty, ZType 0)
   in ZForall u <$> local (environment . at s ?~ u') (evaluateType z)
evaluateType (ZFunction a b) = ZFunction <$> evaluateType a <*> evaluateType b
evaluateType (ZImplicit a b) = ZImplicit <$> evaluateType a <*> evaluateType b
evaluateType (ZPair a b) = ZPair <$> evaluateType a <*> evaluateType b
evaluateType (ZValue a) = unwrapType <$> evaluate a
evaluateType z = pure z

analyzeQuoted :: Raw l -> Untyped l
analyzeQuoted (RUnit :# l) = EUnit :# l
analyzeQuoted (RSymbol s :# l) = ESymbol s :# l
analyzeQuoted (RPair x y :# l) = EPair (analyzeQuoted x) (analyzeQuoted y) :# l

analyzeQQuoted :: (MonadEvaluator l m) => Raw l -> m (Untyped l)
analyzeQQuoted (RUnit :# l) = pure (EUnit :# l)
analyzeQQuoted (RSymbol s :# l) = pure (ESymbol s :# l)
analyzeQQuoted (RS "unquote" `RPair` (y :. RU) :# l) =
  (:# l) . EUnquote <$> analyzeUntyped y
analyzeQQuoted ((RS "unquote-splicing" `RPair` (y :. RU) :# lq) `RPair` r :# l) = do
  y' <- (:# lq) . EUnquoteSplicing <$> analyzeUntyped y
  r' <- analyzeQQuoted r
  pure (EPair y' r' :# l)
analyzeQQuoted (RPair x y :# l) =
  (:# l) <$> (EPair <$> analyzeQQuoted x <*> analyzeQQuoted y)

analyzeUntyped :: (MonadEvaluator l m) => Raw l -> m (Untyped l)
analyzeUntyped (RUnit :# l) = pure (EUnit :# l)
analyzeUntyped (RSymbol s :# l) = pure $ ESymbol s :# l
analyzeUntyped (RS "lambda" `RPair` (RS x :. e :. RU) :# l) =
  (:# l) <$> (ELambda1 (Variable x) <$> analyzeUntyped e <*> pure mempty)
analyzeUntyped (RS "lambda" `RPair` (mxs :. e :. RU) :# l)
  | Just xs <- maybeList mxs,
    Just vs <- traverse maybeSymbol xs =
    (:# l) <$> (ELambdaN (Variable <$> vs) <$> analyzeUntyped e <*> pure mempty)
analyzeUntyped r@(RS "lambda" `RPair` _ :# _) = throwError (InvalidLambda r)
analyzeUntyped (RS "implicit" `RPair` (RS x :. e :. RU) :# l) =
  (:# l) <$> (EImplicit (Variable x) <$> analyzeUntyped e)
analyzeUntyped (RS "macro" `RPair` (RS x :. e :. RU) :# l) =
  (:# l) <$> (EMacro1 (Variable x) <$> analyzeUntyped e <*> pure mempty)
analyzeUntyped (RS "macro" `RPair` (mxs :. e :. RU) :# l)
  | Just xs <- maybeList mxs,
    Just vs <- traverse maybeSymbol xs =
    (:# l) <$> (EMacroN (Variable <$> vs) <$> analyzeUntyped e <*> pure mempty)
analyzeUntyped r@(RS "macro" `RPair` _ :# _) = throwError (InvalidMacro r)
analyzeUntyped (RS ":" `RPair` (e :. t :. RU) :# l) =
  (:# l) <$> (EAnnotation <$> analyzeUntyped e <*> analyzeType t)
analyzeUntyped (RS "quote" `RPair` (x :. RU) :# l) =
  pure $ EQuote (analyzeQuoted x) :# l
analyzeUntyped (RS "quasiquote" `RPair` (x :. RU) :# l) =
  (:# l) <$> (EQuasiQuote <$> analyzeQQuoted x)
analyzeUntyped (RS "forall" `RPair` (RS u :. z :. RU) :# l) =
  (\t -> EType (ZForall (Universal u) t) :# l) <$> analyzeType z
analyzeUntyped (RS "->" `RPair` (a :. b :. RU) :# l) =
  liftA2 (\x y -> EType (ZFunction x y) :# l) (analyzeType a) (analyzeType b)
analyzeUntyped (RS "=>" `RPair` (a :. b :. RU) :# l) =
  liftA2 (\x y -> EType (ZImplicit x y) :# l) (analyzeType a) (analyzeType b)
analyzeUntyped (RPair a b :# l) =
  case maybeList b of
    Just xs -> (:# l) <$> (EApplyN <$> analyzeUntyped a <*> traverse analyzeUntyped xs)
    Nothing -> (:# l) <$> (EApply1 <$> analyzeUntyped a <*> analyzeUntyped b)

analyzeType :: (MonadEvaluator l m) => Raw l -> m (ZType (Untyped l))
analyzeType r = unwrapUntype <$> analyzeUntyped r
  where
    unwrapUntype :: Untyped l -> ZType (Untyped l)
    unwrapUntype ((EType z) :# _) = z
    unwrapUntype v = ZValue v

maybeSymbol :: Raw l -> Maybe Symbol
maybeSymbol (RSymbol s :# _) = Just s
maybeSymbol _ = Nothing

evaluateRaw :: (MonadEvaluator l m) => Maybe (Symbol, Raw l) -> Raw l -> m (Typed l)
evaluateRaw m x = do
  x' <- case m of
    Just (n, t) -> do
      ut <- analyzeUntyped t
      wt <- evaluate =<< liftChecker [] (ut `check` ZAnyType)
      let t' = unwrapType wt
      ur <- analyzeUntyped x
      r <- evaluate =<< infer =<< liftChecker [(n, t')] (ur `check` t')
      pure $ setType t' r
    Nothing -> do
      ux <- analyzeUntyped x
      evaluate =<< infer =<< liftChecker [] (synthesize ux)
  pure (omap universalize x')
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

macroExpand1 :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand1 = go
  where
    go a@(RS "quote" :. _) = pure a
    go (q@(RS "quasiquote") `RPair` r :# l) = (:# l) . RPair q <$> qqExpand r
    go (RPair a@(RS s) b :# lq) = do
      let r' = RPair a (quoteList b) :# lq
      f <- view (environment . at s)
      case f of
        Just (EMacro1 {} :@ _) -> do
          u <- analyzeUntyped r'
          t <- evaluate =<< liftChecker [] (synthesize u)
          pure $ toRaw t
        Just (EMacroN {} :@ (_, ZFunction _ _)) -> do
          u <- analyzeUntyped r'
          t <- evaluate =<< liftChecker [] (synthesize u)
          pure $ toRaw t
        _ -> (:# lq) . RPair a <$> goInner b
    go (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    go r = pure r

    goInner (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    goInner r = pure r

    qqExpand (RPair u@(RS "unquote") b :# l) = (:# l) . RPair u <$> go b
    qqExpand (RPair u@(RS "unquote-splicing") b :# l) = (:# l) . RPair u <$> go b
    qqExpand (RPair a b :# l) = (:# l) <$> (RPair <$> qqExpand a <*> qqExpand b)
    qqExpand q = pure q

    quote e@(_ :# l) = rawTuple (RSymbol "quote" :# locBegin l :| [e])

    quoteList (RPair x y :# l) = RPair (quote x) (quoteList y) :# l
    quoteList e@(RSymbol _ :# _) = quote e
    quoteList e@(RUnit :# _) = e

    toRaw (EUnit :@ (l, _)) = RUnit :# l
    toRaw (ESymbol s :@ (l, _)) = RSymbol s :# l
    toRaw (EPair x y :@ (l, _)) = RPair (toRaw x) (toRaw y) :# l
    toRaw _ = bug Unreachable

macroExpand :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand w = do
  w' <- macroExpand1 w
  if w == w'
    then pure w
    else macroExpand w'

evaluateTopLevel' ::
  ( MonadState (ZState l) m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Raw l ->
  m Typed'
evaluateTopLevel' (RS "def" :. RS s :. e :. RU) = do
  e' <- freezeState $ evaluateRaw Nothing e
  environment . at s ?= e'
  pure (EUnit :$ ZUnit)
evaluateTopLevel' (RS "def" :. RS s :. t :. e :. RU) = do
  e' <- freezeState $ evaluateRaw (Just (s, t)) e
  let e_env = injectEnv e_env e'
  environment . at s ?= e_env
  pure (EUnit :$ ZUnit)
  where
    injectEnv :: Typed l -> Typed l -> Typed l
    injectEnv ee (ELambda1 v x env :@ lt) =
      ELambda1 v (injectEnv ee x) (insert s ee env) :@ lt
    injectEnv ee (ELambdaN vs x env :@ lt) =
      ELambdaN vs (injectEnv ee x) (insert s ee env) :@ lt
    injectEnv e' (EImplicit v x :@ lt) =
      EImplicit v (injectEnv e' x) :@ lt
    injectEnv _ x = x
evaluateTopLevel' (RS "begin" :. r) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel' rs'
        pure $ last xs
      Nothing -> pure (EUnit :$ ZUnit)
    Nothing -> throwError (BadBegin r)
evaluateTopLevel' e = project <$> freezeState (evaluateRaw Nothing e)

evaluateTopLevel ::
  ( MonadState (ZState l) m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Raw l ->
  m Typed'
evaluateTopLevel r = do
  r' <- freezeState (macroExpand r)
  evaluateTopLevel' r'
