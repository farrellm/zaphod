module Zaphod.Types.Error where

import Zaphod.Types.Expr (NativeException, Typed', Untyped', ZType)
import Zaphod.Types.Raw (Raw)
import Zaphod.Types.Wrapper (Existential, Variable)

data ZaphodBug
  = Unreachable
  | NotImplemented Text
  | MissingExistential Existential
  deriving (Show)

instance Exception ZaphodBug

data EvaluatorException l
  = NoMatches ZType
  | MultipleMatches ZType [Typed']
  | InvalidParameters (Raw l)
  | NotList (Raw l)
  | BadBegin (Raw l)
  | NativeException (NativeException l)
  | CheckerException (CheckerException l)
  | InvalidLambda (Raw l)
  | InvalidMacro (Raw l)
  deriving (Functor)

data CheckerException l
  = ArgumentMissmatch [Variable] ZType
  | CannotApply ZType Untyped' l
  | TypeError ZType ZType l
  | NotSubtype ZType ZType l
  | UndefinedVariable Variable
  | ExistentialAlreadySolved ZType Existential ZType
  deriving (Show, Functor)

mapError :: (MonadError a m) => (b -> a) -> ExceptT b m c -> m c
mapError f x = do
  res <- runExceptT x
  case res of
    Right r -> pure r
    Left e -> throwError (f e)
