{-# LANGUAGE LambdaCase #-}

module Zaphod.Types.Error where

import Control.Monad.Except (MonadError (catchError))
import Zaphod.Types.Expr (NativeException, Typed', Untyped, Untyped', ZType)
import Zaphod.Types.Raw (Raw)
import Zaphod.Types.Wrapper (Existential, Variable)

data ZaphodBug
  = Unreachable
  | NotImplemented Text
  | MissingExistential Existential
  deriving (Show)

instance Exception ZaphodBug

data EvaluatorException l
  = NoMatches (ZType Typed') l
  | MultipleMatches (ZType Typed') [ZType Typed'] l
  | InvalidParameters (Raw l)
  | NotList (Raw l)
  | BadBegin (Raw l)
  | NativeException (NativeException l)
  | CheckerException (CheckerException l)
  | InvalidLambda (Raw l)
  | InvalidMacro (Raw l)
  | InvalidCase (Raw l)
  | PatternMatchingFailure (Untyped l) l
  | CallSite l (EvaluatorException l)
  deriving (Functor)

data CheckerException l
  = CannotApply (ZType Typed') Untyped' l
  | TypeError (ZType Typed') (ZType Typed') l
  | NotSubtype (ZType Typed') (ZType Typed') l
  | UndefinedVariable Variable l
  | ExistentialAlreadySolved (ZType Typed') Existential (ZType Typed') l
  | UnquoteOutsideQuasiquote (Untyped l)
  | CheckerEvaluatorExc (EvaluatorException l)
  | InvalidCasePattern (Untyped l)
  deriving (Functor)

withErrorLocation :: (Functor f, MonadError (f l) m) => l -> ExceptT (f ()) m a -> m a
withErrorLocation l x =
  runExceptT x >>= \case
    Right res -> pure res
    Left err -> throwError (l <$ err)

-- taken from mtl-2.3 until I can upgrade

-- | 'MonadError' analogue to the 'Control.Exception.try' function.
tryError :: MonadError e m => m a -> m (Either e a)
tryError action = (Right <$> action) `catchError` (pure . Left)

-- | 'MonadError' analogue to the 'withExceptT' function.
-- Modify the value (but not the type) of an error.  The type is
-- fixed because of the functional dependency @m -> e@.  If you need
-- to change the type of @e@ use 'mapError'.
withError :: MonadError e m => (e -> e) -> m a -> m a
withError f action = tryError action >>= either (throwError . f) pure
