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
import Lens.Micro.Mtl ((%=))
import Relude.Extra (secondF)
import Relude.Extra.Map (elems, insert, lookup, (!?))
import Zaphod.Base (zTrue)
import Zaphod.Checker (check, subtype, synthesize)
import Zaphod.Context ((<:))
import Zaphod.Types

type MonadEvaluator l m =
  ( MonadReader (Environment Typed') m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
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

liftNative :: (MonadError (EvaluatorException l) m) => l -> Either (NativeException ()) a -> m a
liftNative l = liftEither . first (NativeException . fmap (const l))

liftNative' :: (MonadError (EvaluatorException l) m) => Either (NativeException l) a -> m a
liftNative' = liftEither . first NativeException

isSubtype ::
  (MonadReader (Environment Typed') m, MonadError (EvaluatorException ()) m) =>
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

evaluate :: forall l m. (MonadEvaluator l m) => Typed l -> m (Typed l)
evaluate ex@(_ :# (lex, _)) = do
  env <- ask
  runReaderT (eval ex) (mempty, env)
  where
    eval :: Typed l -> ReaderT (Environment (Typed l), Environment Typed') m (Typed l)
    eval (ESymbol s :# (_, z)) = do
      (m, n) <- bimapF (!? s) (!? s) ask
      pure $ case (m, n) of
        (Just v, _) -> setType z v
        (_, Just v) -> setType z $ embed v
        (_, _) -> bug Unreachable
    eval (EAnnotation v z :# _) = setType z <$> eval v
    eval (EApplyN o xs :# lt)
      | ESymbol "if" :# _ <- o =
        case xs of
          p :| [a, b] -> do
            p' <- eval p
            if project p' == zTrue
              then eval a
              else eval b
          _ -> bug Unreachable
      | ESymbol "apply" :# _ <- o,
        f :| [xs'] <- xs =
        eval (EApply1 f xs' :# lt)
    eval (EApply1 f x :# (l, r)) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda1 (Variable v) e env :# _ -> do
          x' <- eval x
          local (\(_, n) -> (insert v x' env, n)) $ eval e
        ELambdaN vs e env :# _ -> do
          mxs' <- eval x
          case nonEmpty <$> maybeList mxs' of
            Just (Just xs') ->
              local (\(_, n) -> (foldl' insertVar env (zip vs $ toList xs'), n)) $
                eval e
            Just Nothing -> eval e
            Nothing -> bug Unreachable
        EMacro1 (Variable v) e :# _ -> do
          x' <- eval x
          local (\(_, n) -> (insert v x' mempty, n)) $ eval e
        EMacroN vs e :# _ -> do
          mxs' <- eval x
          case nonEmpty <$> maybeList mxs' of
            Just (Just xs') ->
              local (\(_, n) -> (foldl' insertVar mempty (zip vs $ toList xs'), n)) $
                eval e
            Just Nothing -> eval e
            Nothing -> bug Unreachable
        EImplicit (Variable v) e env :# (_, ZImplicit i _) -> do
          ss <- findOfType i
          case ss of
            [s] ->
              local (\(_, n) -> (insert v (embed s) env, n)) $
                eval (EApply1 e x :# (l, r))
            [] -> throwError (NoMatches i)
            _ -> throwError (MultipleMatches i ss)
        ENative (Native g) :# _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a] -> liftNative l $ setLocation l <$> g (project a)
            _ -> bug Unreachable
        ENative' (Native' g) :# _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a] -> liftNative' $ g a
            _ -> bug Unreachable
        ENativeIO (NativeIO g) :# _ -> setLocation l <$> liftIO g
        _ -> bug Unreachable
    eval (EApplyN f xs :# (l, r)) = do
      f' <- eval f
      setType r <$> case f' of
        ELambda1 (Variable v) e env :# _ -> do
          x' <- eval (typedTuple xs)
          local (\(_, n) -> (insert v x' env, n)) $ eval e
        ELambdaN vs e env :# _ -> do
          xs' <- traverse eval xs
          local (\(_, n) -> (foldl' insertVar env (zip vs $ toList xs'), n)) $ eval e
        EMacro1 (Variable v) e :# _ -> do
          x' <- eval (typedTuple xs)
          local (\(_, n) -> (insert v x' mempty, n)) $ eval e
        EMacroN vs e :# _ -> do
          xs' <- traverse eval xs
          local (\(_, n) -> (foldl' insertVar mempty (zip vs $ toList xs'), n)) $ eval e
        EImplicit (Variable v) e env :# (_, ZImplicit i _) -> do
          ss <- findOfType i
          case ss of
            [s] ->
              local (\(_, n) -> (insert v (embed s) env, n)) $
                eval (EApplyN e xs :# (l, r))
            [] -> throwError (NoMatches i)
            _ -> throwError (MultipleMatches i ss)
        ENative (Native g) :# _ ->
          case xs of
            x :| [] -> do
              x' <- eval x
              liftNative l $ setLocation l <$> g (project x')
            _ -> do
              xs' <- eval (typedTuple xs)
              liftNative l $ setLocation l <$> g (project xs')
        ENative' (Native' g) :# _ ->
          case xs of
            x :| [] -> do
              x' <- eval x
              liftNative' $ g x'
            _ -> do
              xs' <- eval (typedTuple xs)
              liftNative' $ g xs'
        ENativeIO (NativeIO g) :# _ -> setLocation l <$> liftIO g
        _ -> trace' (render (project f' :: Typed')) $ bug Unreachable
    eval (EPair a b :# lt) = (:# lt) <$> (EPair <$> eval a <*> eval b)
    eval (ELambda1 v e _ :# lt) = (:# lt) <$> (ELambda1 v e <$> (fst <$> ask))
    eval (ELambdaN vs e _ :# lt) = (:# lt) <$> (ELambdaN vs e <$> (fst <$> ask))
    eval (EQuote z :# _) = pure z
    eval (EType t :# l) = (:# l) . EType <$> evalType t
    eval e = pure e

    evalType :: ZType -> ReaderT (Environment (Typed l), Environment Typed') m ZType
    evalType (ZForall u@(Universal s) z) =
      ZForall u <$> local (first (insert s (EType (ZUniversal u) :# (mempty, ZType 0)))) (evalType z)
    evalType (ZFunction a b) = ZFunction <$> evalType a <*> evalType b
    evalType (ZImplicit a b) = ZImplicit <$> evalType a <*> evalType b
    evalType (ZPair a b) = ZPair <$> evalType a <*> evalType b
    evalType (ZValue a) = unwrapType <$> eval (embed a)
    evalType (ZUntyped _) = bug Unreachable
    evalType z = pure z

    findOfType z = do
      (lcl, gbl) <- ask
      let env = (project <$> lcl) <> gbl
      mapError (const lex <$>) . usingReaderT env $
        filterM (isSubtype z . exprType') (elems env)

    insertVar :: Environment a -> (Variable, a) -> Environment a
    insertVar env (Variable v, x) = insert v x env

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
analyzeType x@(RS _) = ZUntyped . project <$> analyzeUntyped x
analyzeType (RS "_forall" :. RS u :. z :. RU) = ZForall (Universal u) <$> analyzeType z
analyzeType (RS "->" :. a :. b :. RU) = ZFunction <$> analyzeType a <*> analyzeType b
analyzeType (RS "=>" :. a :. b :. RU) = ZImplicit <$> analyzeType a <*> analyzeType b
analyzeType (RS "quote" :. x :. RU) =
  pure . ZUntyped . LocU $ EQuote (LocU $ EType (quoteType x))
  where
    quoteType :: Raw l -> ZType
    quoteType RU = ZUnit
    quoteType (l :. r) = ZPair (quoteType l) (quoteType r)
    quoteType (RS s) = ZValue $ ESymbol s :# ((), ZSymbol)
analyzeType (RPair (RSymbol "cons" :# lc) ts :# lp) =
  analyzeType (RPair (RSymbol "zcons" :# lc) ts :# lp)
analyzeType (a :. b) = do
  a' <- analyzeUntyped a
  case nonEmpty <$> maybeList b of
    Just (Just xs) -> do
      xs' <- traverse (fmap unwrapUntyped . analyzeType) xs
      pure . ZUntyped . LocU $ EApplyN (project a') xs'
    Just Nothing -> pure . ZUntyped . LocU $ EApply1 (project a') (LocU EUnit)
    Nothing -> do
      b' <- analyzeType b
      pure . ZUntyped . LocU $ EApply1 (project a') (LocU $ EType b')

analyzeQuoted :: Raw l -> Untyped l
analyzeQuoted (RUnit :# l) = EUnit :# l
analyzeQuoted (RSymbol s :# l) = ESymbol s :# l
analyzeQuoted (RPair x y :# l) = EPair (analyzeQuoted x) (analyzeQuoted y) :# l

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
  (:# l) <$> (EImplicit (Variable x) <$> analyzeUntyped e <*> pure mempty)
analyzeUntyped (RS "macro" `RPair` (RS x :. e :. RU) :# l) =
  (:# l) <$> (EMacro1 (Variable x) <$> analyzeUntyped e)
analyzeUntyped (RS "macro" `RPair` (mxs :. e :. RU) :# l)
  | Just xs <- maybeList mxs,
    Just vs <- traverse maybeSymbol xs =
    (:# l) <$> (EMacroN (Variable <$> vs) <$> analyzeUntyped e)
analyzeUntyped r@(RS "macro" `RPair` _ :# _) = throwError (InvalidMacro r)
analyzeUntyped (RS ":" `RPair` (t :. RS "Type" :. RU) :# l) =
  (:# l) . EType <$> analyzeType t
analyzeUntyped (RS ":" `RPair` (e :. t :. RU) :# l) =
  (:# l) <$> (EAnnotation <$> analyzeUntyped e <*> evaluateRawType t)
analyzeUntyped (RS "quote" `RPair` (x :. RU) :# l) =
  pure $ EQuote (analyzeQuoted x) :# l
analyzeUntyped (RPair a b :# l) =
  case nonEmpty <$> maybeList b of
    Just (Just xs) ->
      (:# l) <$> (EApplyN <$> analyzeUntyped a <*> traverse analyzeUntyped xs)
    Just Nothing ->
      (:# l) <$> (EApply1 <$> analyzeUntyped a <*> pure (EUnit :# locEnd l))
    Nothing -> (:# l) <$> (EApply1 <$> analyzeUntyped a <*> analyzeUntyped b)

maybeSymbol :: Raw l -> Maybe Symbol
maybeSymbol (RSymbol s :# _) = Just s
maybeSymbol _ = Nothing

evaluateRaw ::
  ( MonadState ZState m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Maybe (Symbol, Raw l) ->
  Raw l ->
  m (Typed l)
evaluateRaw m x@(_ :# l) = do
  env <- _environment <$> get
  x' <-
    usingReaderT env
      . evaluatingStateT (emptyCheckerState env)
      $ case m of
        Just (n, RSymbol "Type" :# _) -> do
          context %= (CVariable (Variable n) (ZType 0) <:)
          (:# (l, ZType 0)) . EType <$> evaluateRawType x
        Just (n, t) -> do
          t' <- evaluateRawType t
          context %= (CVariable (Variable n) t' <:)
          r <- evaluate =<< liftChecker (`check` t') =<< analyzeUntyped x
          pure $ setType t' r
        Nothing -> evaluate =<< liftChecker synthesize =<< analyzeUntyped x
  pure (secondF universalize x')
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
evaluateRawType t@(_ :# l) = do
  t' <- analyzeType t
  evaluateType . setLocation' l $ unwrapUntyped t'

macroExpand1 :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand1 w = do
  env <- ask
  evaluatingStateT (emptyCheckerState env) $ go w
  where
    go a@(RS "quote" :. _) = pure a
    go (RPair a@(RS s) b :# lq) = do
      let r' = RPair a (quoteList b) :# lq
      f <- lookup s <$> ask
      case f of
        Just (EMacro1 {} :# _) ->
          toRaw <$> (evaluate =<< liftChecker synthesize =<< analyzeUntyped r')
        Just (EMacroN _ _ :# (ZFunction _ _)) ->
          toRaw <$> (evaluate =<< liftChecker synthesize =<< analyzeUntyped r')
        _ -> (:# lq) . RPair a <$> goInner b
    go (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    go r = pure r

    goInner (RPair x y :# l) = (:# l) <$> (RPair <$> go x <*> goInner y)
    goInner r = pure r

    quote e@(_ :# l) = rawTuple (RSymbol "quote" :# locBegin l :| [e])

    quoteList (RPair x y :# l) = RPair (quote x) (quoteList y) :# l
    quoteList e@(RSymbol _ :# _) = quote e
    quoteList e@(RUnit :# _) = e

    toRaw (EUnit :# (l, _)) = RUnit :# l
    toRaw (ESymbol s :# (l, _)) = RSymbol s :# l
    toRaw (EPair x y :# (l, _)) = RPair (toRaw x) (toRaw y) :# l
    toRaw _ = bug Unreachable

macroExpand :: (MonadEvaluator l m) => Raw l -> m (Raw l)
macroExpand w = do
  w' <- macroExpand1 w
  if project w == (project w' :: Raw')
    then pure w
    else macroExpand w'

evaluateTopLevel' ::
  ( MonadState ZState m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Raw l ->
  m Typed'
evaluateTopLevel' (RS "def" :. RS s :. e :. RU) = do
  e' <- evaluateRaw Nothing e
  environment %= insert s (project e')
  pure (EUnit :# ZUnit)
evaluateTopLevel' (RS "def" :. RS s :. t :. e :. RU) = do
  e' <- evaluateRaw (Just (s, t)) e
  environment %= insert s (project e')
  pure (EUnit :# ZUnit)
evaluateTopLevel' (RS "begin" :. r) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel' rs'
        pure $ last xs
      Nothing -> throwError (BadBegin r)
    Nothing -> throwError (BadBegin r)
evaluateTopLevel' e = project <$> evaluateRaw Nothing e

evaluateTopLevel ::
  ( MonadState ZState m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  ) =>
  Raw l ->
  m Typed'
evaluateTopLevel r = do
  env <- _environment <$> get
  r' <- runReaderT (macroExpand r) env
  evaluateTopLevel' r'
