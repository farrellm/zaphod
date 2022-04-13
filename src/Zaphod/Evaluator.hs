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
import Relude.Extra.Map (elems, insert, lookup, (!?))
import Zaphod.Base (zTrue)
import Zaphod.Checker (check, subtype, synthesize)
import Zaphod.Context ((<:))
import Zaphod.Types

unwrapType :: Typed l -> ZType (Typed l)
unwrapType ((EType z) :@ _) = z
unwrapType _ = bug Unreachable

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

isSubtype :: (MonadEvaluator l m) => ZType (Typed l) -> ZType (Typed l) -> m Bool
isSubtype a b = do
  gbl <- snd <$> ask
  e <- runExceptT (evaluatingStateT (emptyCheckerState gbl) $ subtype a b)
  case e of
    Right () -> pure True
    Left NotSubtype {} -> pure False
    Left err -> throwError (CheckerException err)

evaluate :: forall l m. (MonadEvaluator l m) => Typed l -> m (Typed l)
evaluate ex@(_ :@ (lex, _)) = eval ex
  where
    eval :: Typed l -> m (Typed l)
    eval (ESymbol s :@ (_, z)) = do
      (m, n) <- bimapF (!? s) (!? s) ask
      pure $ case (m, n) of
        (Just v, _) -> setType z v
        (_, Just v) -> setType z v
        (_, _) -> bug Unreachable
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
    eval (ELambda1 v e _ :@ lt) = (:@ lt) <$> (ELambda1 v e <$> (fst <$> ask))
    eval (ELambdaN vs e _ :@ lt) = (:@ lt) <$> (ELambdaN vs e <$> (fst <$> ask))
    eval (EQuote z :@ _) = pure z
    eval (EType t :@ l) = (:@ l) . EType <$> evaluateType t
    eval e = pure e

    evalApply1 f x l t = do
      f' <- eval f
      setType t <$> case f' of
        ELambda1 (Variable v) e env :@ _ -> do
          x' <- eval x
          modifyError (CallSite l)
            . local (\(_, n) -> (insert v x' env, n))
            $ eval e
        ELambdaN vs e env :@ _ -> do
          mxs' <- eval x
          case nonEmpty <$> maybeList mxs' of
            Just (Just xs') ->
              modifyError (CallSite l)
                . local (\(_, n) -> (foldl' insertVar env (zip vs $ toList xs'), n))
                $ eval e
            Just Nothing -> eval e
            Nothing -> bug Unreachable
        EMacro1 (Variable v) e :@ _ -> do
          x' <- eval x
          modifyError (CallSite l)
            . local (\(_, n) -> (insert v x' mempty, n))
            $ eval e
        EMacroN vs e :@ _ -> do
          mxs' <- eval x
          case maybeList mxs' of
            Just xs' ->
              modifyError (CallSite l)
                . local (\(_, n) -> (foldl' insertVar mempty (zip vs xs'), n))
                $ eval e
            Nothing -> bug Unreachable
        EImplicit (Variable v) e env :@ (_, ZImplicit i _) -> do
          ss <- findOfType i
          case ss of
            [s] ->
              modifyError (CallSite l)
                . local (\(_, n) -> (insert v s env, n))
                $ eval (EApply1 e x :@ (l, t))
            [] -> throwError (NoMatches $ project i)
            _ -> throwError (MultipleMatches (project i) (project <$> ss))
        ENative (Native g) :@ _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a] ->
              modifyError (CallSite l)
                . liftNative l
                $ setLocation l <$> g (project a)
            _ -> bug Unreachable
        ENative' (Native' g) :@ _ -> do
          x' <- eval x
          case maybeList x' of
            Just [a] ->
              modifyError (CallSite l)
                . liftNative l
                $ g a
            _ -> bug Unreachable
        ENativeIO (NativeIO g) :@ _ ->
          modifyError (CallSite l) $
            setLocation l <$> liftIO g
        _ -> bug Unreachable

    evalApplyN f xs l t = do
      f' <- eval f
      setType t <$> case f' of
        ELambda1 (Variable v) e env :@ _ -> do
          x' <- eval (typedTuple xs)
          modifyError (CallSite l)
            . local (\(_, n) -> (insert v x' env, n))
            $ eval e
        ELambdaN vs e env :@ _ -> do
          xs' <- traverse eval xs
          modifyError (CallSite l)
            . local (\(_, n) -> (foldl' insertVar env (zip vs xs'), n))
            $ eval e
        EMacro1 (Variable v) e :@ _ -> do
          x' <- eval (typedTuple xs)
          modifyError (CallSite l)
            . local (\(_, n) -> (insert v x' mempty, n))
            $ eval e
        EMacroN vs e :@ _ -> do
          xs' <- traverse eval xs
          modifyError (CallSite l)
            . local (\(_, n) -> (foldl' insertVar mempty (zip vs xs'), n))
            $ eval e
        EImplicit (Variable v) e env :@ (_, ZImplicit i _) -> do
          ss <- findOfType i
          case ss of
            [s] ->
              modifyError (CallSite l)
                . local (\(_, n) -> (insert v s env, n))
                $ eval (EApplyN e xs :@ (l, t))
            [] -> throwError (NoMatches $ project i)
            _ -> throwError (MultipleMatches (project i) (project <$> ss))
        ENative (Native g) :@ _ ->
          case xs of
            [x] -> do
              x' <- eval x
              modifyError (CallSite l)
                . liftNative l
                $ setLocation l <$> g (project x')
            _ -> do
              xs' <- eval (typedTuple xs)
              liftNative l $ setLocation l <$> g (project xs')
        ENative' (Native' g) :@ _ ->
          case xs of
            [x] -> do
              x' <- eval x
              modifyError (CallSite l)
                . liftNative l
                $ g x'
            _ -> do
              xs' <- eval (typedTuple xs)
              modifyError (CallSite l)
                . liftNative l
                $ g xs'
        ENativeIO (NativeIO g) :@ _ ->
          modifyError (CallSite l) $
            setLocation l <$> liftIO g
        _ -> debug (render f') $ bug Unreachable

    findOfType :: ZType (Typed l) -> m [Typed l]
    findOfType z = do
      gbl <- snd <$> ask
      mapError (const lex <$>) $
        filterM (isSubtype z . exprType) (elems gbl)

    insertVar :: Environment a -> (Variable, a) -> Environment a
    insertVar env (Variable v, x) = insert v x env

evaluateType :: (MonadEvaluator l m) => ZType (Typed l) -> m (ZType (Typed l))
evaluateType (ZForall u@(Universal s) z) = do
  let u' = EType (ZUniversal u) :@ (mempty, ZType 0)
   in ZForall u <$> local (first (insert s u')) (evaluateType z)
evaluateType (ZFunction a b) = ZFunction <$> evaluateType a <*> evaluateType b
evaluateType (ZImplicit a b) = ZImplicit <$> evaluateType a <*> evaluateType b
evaluateType (ZPair a b) = ZPair <$> evaluateType a <*> evaluateType b
evaluateType (ZValue a) = unwrapType <$> evaluate a
evaluateType z = pure z

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
analyzeUntyped (RS ":" `RPair` (e :. t :. RU) :# l) =
  (:# l) <$> (EAnnotation <$> analyzeUntyped e <*> analyzeType t)
analyzeUntyped (RS "quote" `RPair` (x :. RU) :# l) =
  pure $ EQuote (analyzeQuoted x) :# l
analyzeUntyped (RS "_forall" `RPair` (RS u :. z :. RU) :# l) =
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
  gbl <- snd <$> ask
  x' <- evaluatingStateT (emptyCheckerState gbl) $
    case m of
      Just (n, t) -> do
        t' <- evaluate =<< liftChecker (`check` ZAnyType) =<< analyzeUntyped t
        let t'' = unwrapType t'
        context %= (CVariable (Variable n) t'' <:)
        r <- evaluate =<< liftChecker (`check` t'') =<< analyzeUntyped x
        pure $ setType t'' r
      Nothing -> evaluate =<< liftChecker synthesize =<< analyzeUntyped x
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
macroExpand1 w = do
  gbl <- snd <$> ask
  evaluatingStateT (emptyCheckerState gbl) $ go w
  where
    go a@(RS "quote" :. _) = pure a
    go (RPair a@(RS s) b :# lq) = do
      let r' = RPair a (quoteList b) :# lq
      f <- lookup s . snd <$> ask
      case f of
        Just (EMacro1 {} :@ _) ->
          toRaw <$> (evaluate =<< liftChecker synthesize =<< analyzeUntyped r')
        Just (EMacroN _ _ :@ (_, ZFunction _ _)) ->
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

withEnvironment ::
  (MonadState (ZState l) m) =>
  ReaderT (Environment (Typed l), Environment (Typed l)) m a ->
  m a
withEnvironment x = do
  env <- _environment <$> get
  usingReaderT (mempty, env) x

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
  e' <- withEnvironment $ evaluateRaw Nothing e
  environment %= insert s e'
  pure (EUnit :$ ZUnit)
evaluateTopLevel' (RS "def" :. RS s :. t :. e :. RU) = do
  e' <- withEnvironment $ evaluateRaw (Just (s, t)) e
  environment %= insert s e'
  pure (EUnit :$ ZUnit)
evaluateTopLevel' (RS "begin" :. r) =
  case maybeList r of
    Just rs -> case nonEmpty rs of
      Just rs' -> do
        xs <- traverse evaluateTopLevel' rs'
        pure $ last xs
      Nothing -> pure (EUnit :$ ZUnit)
    Nothing -> throwError (BadBegin r)
evaluateTopLevel' e = project <$> withEnvironment (evaluateRaw Nothing e)

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
  r' <- withEnvironment (macroExpand r)
  evaluateTopLevel' r'
