{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Evaluator
  ( evaluate,
    infer,
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
import Relude.Extra.Bifunctor (secondF)
import Relude.Extra.Map (insert, toPairs)
import Zaphod.Checker (check, isSubtype, retype, synthesize)
import Zaphod.Context ((<:))
import Zaphod.Types

unwrapType :: Untyped l -> ZType (Untyped l)
unwrapType ((EType z) :# _) = z
unwrapType v = ZValue v

liftChecker ::
  (MonadEvaluator l m) =>
  [(Symbol, ZType (Typed l))] ->
  ExceptT (CheckerException l) (StateT (CheckerState l) m) b ->
  m b
liftChecker bs x = do
  ctx <- view envContext
  e <- evaluatingStateT (emptyCheckerState ctx) $ do
    for_ bs $ \(n, t) ->
      context %= (CVariable (Variable n) t <:)
    runExceptT x
  case e of
    Right res -> pure res
    Left err -> throwError (CheckerException err)

liftNative :: (MonadError (EvaluatorException l) m) => l -> Either (NativeException ()) a -> m a
liftNative l = liftEither . first (NativeException . fmap (const l))

findOfType :: (MonadEvaluator l m) => l -> ZType (Typed l) -> m Symbol
findOfType l z = do
  vs <- view (envContext . to toPairs)
  xs <- liftChecker [] . withErrorLocation l $ filterM (isSubtype z . snd) vs
  case xs of
    [x] -> pure $ fst x
    [] -> throwError (NoMatches (project z) l)
    _ -> throwError (MultipleMatches (project z) (project . snd <$> xs) l)

infer :: (MonadEvaluator l m) => Typed l -> m (Untyped l)
infer (EImplicit v@(Variable s) e :@ (l, ZImplicit a _)) = do
  e' <- local (envContext . at s ?~ a) $ infer e
  pure (EImplicit v e' :# l)
infer (EImplicit {} :@ _) = bug Unreachable
infer (EApplyN f@(_ :@ (l, ZImplicit a _)) xs :@ (la, _)) = do
  i <- findOfType l a
  f' <- infer f
  xs' <- traverse infer xs
  pure (EApplyN (EApply1 f' (ESymbol i :# l) :# la) xs' :# la)
infer (EUnit :@ (l, _)) = pure (EUnit :# l)
infer (ESymbol s :@ (l, _)) = pure (ESymbol s :# l)
infer (EAnnotation a _ :@ _) = infer a
infer (ELambda1 v e _ :@ (l, _)) = (:# l) <$> (ELambda1 v <$> infer e <*> pure mempty)
infer (ELambdaN vs e _ :@ (l, _)) = (:# l) <$> (ELambdaN vs <$> infer e <*> pure mempty)
infer (EMacro e :@ (l, _)) = (:# l) . EMacro <$> infer e
infer (ENative f :@ (l, _)) = pure (ENative f :# l)
infer (ENative' f :@ (l, _)) = pure (ENative' f :# l)
infer (ENativeIO f :@ (l, _)) = pure (ENativeIO f :# l)
infer (EApply1 f e :@ (l, _)) = (:# l) <$> (EApply1 <$> infer f <*> infer e)
infer (EApplyN f es :@ (l, _)) = (:# l) <$> (EApplyN <$> infer f <*> traverse infer es)
infer (EPair a b :@ (l, _)) = (:# l) <$> (EPair <$> infer a <*> infer b)
infer (EType t :@ (l, _)) = (:# l) . EType <$> traverse infer t
infer (ECase e xs :@ (l, _)) = (:# l) <$> (ECase <$> infer e <*> traverse infer2 xs)
  where
    infer2 (x, y) = (,) <$> infer x <*> infer y
infer q@(EQuote {} :@ _) = pure (project q)
infer (EQuasiQuote q :@ (l, _)) = (:# l) . EQuasiQuote <$> inferQQ q
  where
    inferQQ (EUnit :@ (m, _)) = pure (EUnit :# m)
    inferQQ (ESymbol s :@ (m, _)) = pure (ESymbol s :# m)
    inferQQ (EPair a b :@ (m, _)) = (:# m) <$> (EPair <$> inferQQ a <*> inferQQ b)
    inferQQ (EUnquote s :@ (m, _)) = (:# m) . EUnquote <$> infer s
    inferQQ (EUnquoteSplicing s :@ (m, _)) = (:# m) . EUnquoteSplicing <$> infer s
    inferQQ e = traceM' (render e) >> bug Unreachable
infer (ESpecial :@ _) = bug Unreachable
infer (EUnquoteSplicing {} :@ _) = bug Unreachable
infer (EUnquote {} :@ _) = bug Unreachable

evaluate :: forall l m. (MonadEvaluator l m) => Untyped l -> m (Untyped l)
evaluate = eval
  where
    eval :: Untyped l -> m (Untyped l)
    -- self evaluating
    eval e@(EUnit :# _) = pure e
    eval e@(EImplicit {} :# _) = pure e
    eval e@(ENative {} :# _) = pure e
    eval e@(ENative' {} :# _) = pure e
    eval e@(ENativeIO {} :# _) = pure e
    -- variables
    eval (ESymbol s :# _) = do
      m <- view (environment . at s)
      case m of
        Just v -> pure v
        _ -> bug Unreachable
    -- apply
    eval (EApply1 f x :# l) = evalApply1 f x l
    eval (EApplyN o xs :# l)
      | ESymbol "apply" :# _ <- o,
        [f, xs'] <- xs =
        eval (EApply1 f xs' :# l)
      | otherwise = evalApplyN o xs l
    -- special forms
    eval (ELambda1 v e _ :# l) = (:# l) <$> (ELambda1 v e <$> view environment)
    eval (ELambdaN vs e _ :# l) = (:# l) <$> (ELambdaN vs e <$> view environment)
    eval (EMacro e :# l) = (:# l) . EMacro <$> eval e
    eval (ECase x (p :| ps) :# l) = evalCase (p : ps) l =<< eval x
    -- types
    eval (EType t :# l) = (:# l) . EType <$> evaluateType t
    -- quoting
    eval (EQuote z :# _) = pure z
    eval (EQuasiQuote q :# _) = evalQQ q
    -- impossible
    eval (EPair {} :# _) = bug Unreachable
    eval (ESpecial :# _) = bug Unreachable
    eval (EAnnotation {} :# _) = bug Unreachable
    eval (EUnquote {} :# _) = bug Unreachable
    eval (EUnquoteSplicing {} :# _) = bug Unreachable

    evalApply1 f x l = do
      f' <- eval f
      x' <- eval x
      withError (CallSite l) $
        case f' of
          ELambda1 (Variable v) e env :# _ ->
            local (environment .~ insert v x' env) $ eval e
          ELambdaN vs e env :# _
            | Just xs' <- maybeList x' ->
              local (environment .~ foldl' insertVar env (zip vs xs')) $ eval e
          EImplicit (Variable v) e :# _ ->
            local (environment %~ insert v x') $ eval e
          ENative (Native g) :# _
            | Just [a] <- maybeList x' ->
              liftNative l $ setLocation l <$> g (project a)
          ENative' (Native' g) :# _
            | Just [a] <- maybeList x' ->
              liftNative l $ g a
          ENativeIO (NativeIO g) :# _ -> setLocation l <$> liftIO g
          _ -> bug Unreachable

    evalApplyN f xs l = do
      f' <- eval f
      xs' <- traverse eval xs
      withError (CallSite l) $
        case f' of
          ELambda1 (Variable v) e env :# _ ->
            local (environment .~ insert v (untypedTuple xs') env) $ eval e
          ELambdaN vs e env :# _ ->
            local (environment .~ foldl' insertVar env (zip vs xs')) $ eval e
          ENative (Native g) :# _ ->
            case xs' of
              [x'] -> liftNative l $ setLocation l <$> g (project x')
              _ -> liftNative l $ setLocation l <$> g (project $ untypedTuple xs')
          ENative' (Native' g) :# _ ->
            case xs' of
              [x'] -> liftNative l $ g x'
              _ -> liftNative l $ g (untypedTuple xs')
          ENativeIO (NativeIO g) :# _ -> setLocation l <$> liftIO g
          _ -> debug (render f') $ bug Unreachable

    evalCase ((p, e) : ps) l x
      | Just bs <- bindings x p =
        local (environment %~ flip (foldl' insertVar) bs) $ eval e
      | otherwise = evalCase ps l x
    evalCase [] l x = traceM' (render x) >> throwError (PatternMatchingFailure x l)

    bindings (EUnit :# _) (EUnit :# _) = Just []
    bindings (ESymbol l :# _) (ESymbol r :# _)
      | isConstructor r && l == r = Just []
    bindings x (ESymbol r :# _)
      | not (isConstructor r) = Just [(Variable r, x)]
    bindings (EPair l r :# _) (EApply1 f x :# _) =
      (++) <$> bindings l f <*> bindings r x
    bindings (EPair l1 r1 :# _) (EApplyN f xs :# _)
      | Just rs <- maybeList r1 =
        (++) <$> bindings l1 f <*> (concat <$> zipWithStrict bindings rs xs)
    bindings _ _ = Nothing

    zipWithStrict :: (a -> b -> Maybe c) -> [a] -> [b] -> Maybe [c]
    zipWithStrict _ [] [] = Just []
    zipWithStrict f (x : xs) (y : ys) =
      (:) <$> f x y <*> zipWithStrict f xs ys
    zipWithStrict _ _ _ = Nothing

    evalQQ e@(EUnit :# _) = pure e
    evalQQ e@(ESymbol _ :# _) = pure e
    evalQQ (EPair (EUnquoteSplicing q :# _) r :# _) = (<>) <$> eval q <*> evalQQ r
    evalQQ (EPair a b :# l) = (:# l) <$> (EPair <$> evalQQ a <*> evalQQ b)
    evalQQ (EUnquote e :# _) = eval e
    evalQQ e = trace' (render e) $ bug Unreachable

    insertVar :: Environment a -> (Variable, a) -> Environment a
    insertVar env (Variable v, x) = insert v x env

evaluateType :: (MonadEvaluator l m) => ZType (Untyped l) -> m (ZType (Untyped l))
evaluateType (ZForall u@(Universal s) z) = do
  let u' = EType (ZUniversal u) :# mempty
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
analyzeUntyped ((RSymbol "macro" :# lm) `RPair` x :# l) =
  (:# l) . EMacro <$> analyzeUntyped ((RSymbol "lambda" :# lm) `RPair` x :# l)
analyzeUntyped r@(RS "macro" `RPair` _ :# _) = throwError (InvalidMacro r)
analyzeUntyped r@(RS "case" `RPair` (x :. rs) :# l)
  | Just cs <- nonEmpty =<< maybeList rs = do
    mcs' <- traverse analyzeCase cs
    case sequence mcs' of
      Just cs' -> (:# l) <$> (ECase <$> analyzeUntyped x <*> pure cs')
      Nothing -> throwError (InvalidCase r)
  where
    analyzeCase (p :. v :. RU) =
      Just <$> ((,) <$> analyzeUntyped p <*> analyzeUntyped v)
    analyzeCase _ = pure Nothing
analyzeUntyped r@(RS "case" :. _) = throwError (InvalidCase r)
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
analyzeUntyped (RPair a b :# l)
  | Just xs <- maybeList b =
    (:# l) <$> (EApplyN <$> analyzeUntyped a <*> traverse analyzeUntyped xs)
  | otherwise = (:# l) <$> (EApply1 <$> analyzeUntyped a <*> analyzeUntyped b)

analyzeType :: (MonadEvaluator l m) => Raw l -> m (ZType (Untyped l))
analyzeType r = unwrapType <$> analyzeUntyped r

maybeSymbol :: Raw l -> Maybe Symbol
maybeSymbol (RSymbol s :# _) = Just s
maybeSymbol _ = Nothing

evaluateRaw :: (MonadEvaluator l m) => Maybe (Symbol, Raw l) -> Raw l -> m (Untyped l, ZType (Typed l))
evaluateRaw m x = do
  secondF universalize $ case m of
    Just (n, t) -> do
      ut <- analyzeUntyped t
      wt <- evaluate =<< infer =<< liftChecker [] (ut `check` ZAnyType)
      let t' = retype $ unwrapType wt
      ur <- analyzeUntyped x
      r <- evaluate =<< infer =<< liftChecker [(n, t')] (ur `check` t')
      pure (r, t')
    Nothing -> do
      ux <- analyzeUntyped x
      tx@(_ :@ (_, t)) <- liftChecker [] (synthesize ux)
      r <- evaluate =<< infer tx
      pure (r, t)
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
    replaceExt eus (ZValue a) = ZValue $ omap (replaceExt eus) a
    replaceExt _ z = z

macroExpand1 :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand1 = go
  where
    go a@(RS "quote" :. _) = pure a
    go (q@(RS "quasiquote") `RPair` r :# l) = (:# l) . RPair q <$> qqExpand r
    go (RPair a@(RS s) b :# lq) = do
      m <- view (environment . at s)
      case m of
        Just (EMacro f :# _) -> do
          b' <- analyzeUntyped $ quote b
          let u = EApply1 f b' :# lq
          x <- evaluate =<< infer =<< liftChecker [] (synthesize u)
          pure $ toRaw x
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

    toRaw (EUnit :# l) = RUnit :# l
    toRaw (ESymbol s :# l) = RSymbol s :# l
    toRaw (EPair x y :# l) = RPair (toRaw x) (toRaw y) :# l
    toRaw e = trace' (render e) $ bug Unreachable

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
  m (Untyped', ZType Typed')
evaluateTopLevel' (RS "def" :. RS s :. e :. RU) = do
  (e', t) <- freezeState $ evaluateRaw Nothing e
  environment . at s ?= e'
  envContext . at s ?= t
  pure (LocU EUnit, ZUnit)
evaluateTopLevel' (RS "def" :. RS s :. t :. e :. RU) = do
  (e', t') <- freezeState $ evaluateRaw (Just (s, t)) e
  let e_env = injectEnv e_env e'
  environment . at s ?= e_env
  envContext . at s ?= t'
  pure (LocU EUnit, ZUnit)
  where
    injectEnv :: Untyped l -> Untyped l -> Untyped l
    injectEnv ee (ELambda1 v x env :# l) =
      ELambda1 v (injectEnv ee x) (insert s ee env) :# l
    injectEnv ee (ELambdaN vs x env :# l) =
      ELambdaN vs (injectEnv ee x) (insert s ee env) :# l
    injectEnv e' (EImplicit v x :# l) =
      EImplicit v (injectEnv e' x) :# l
    injectEnv _ x = x
evaluateTopLevel' (RS "begin" :. r) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel' rs'
        pure $ last xs
      Nothing -> pure (LocU EUnit, ZUnit)
    Nothing -> throwError (BadBegin r)
evaluateTopLevel' e =
  bimapF project project $ freezeState (evaluateRaw Nothing e)

evaluateTopLevel ::
  ( MonadState (ZState l) m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Raw l ->
  m (Untyped', ZType Typed')
evaluateTopLevel r = do
  r' <- freezeState (macroExpand r)
  evaluateTopLevel' r'
