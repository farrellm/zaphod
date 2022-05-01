module Zaphod.Types.Error where

import Control.Monad.Except (MonadError (catchError))
import Zaphod.Types.Expr (NativeException, Typed, Untyped, ZType)
import Zaphod.Types.Raw (Raw)
import Zaphod.Types.Wrapper (Existential, Variable)

data ZaphodBug
  = Unreachable
  | NotImplemented Text
  | MissingExistential Existential
  deriving (Show)

instance Exception ZaphodBug

data EvaluatorException l
  = NoMatches (ZType (Typed l)) l
  | MultipleMatches (ZType (Typed l)) [ZType (Typed l)] l
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
  = CannotApply (ZType (Typed l)) (Untyped l) l
  | TypeError (ZType (Typed l)) (ZType (Typed l)) l
  | NotSubtype (ZType (Typed l)) (ZType (Typed l)) l
  | UndefinedVariable Variable l
  | ExistentialAlreadySolved (ZType (Typed l)) Existential (ZType (Typed l))
  | UnquoteOutsideQuasiquote (Untyped l) l
  | CheckerEvaluatorExc (EvaluatorException l)
  | InvalidCasePattern (Untyped l)
  deriving (Functor)

mapError :: (MonadError a m) => (b -> a) -> ExceptT b m c -> m c
mapError f x = do
  res <- runExceptT x
  case res of
    Right r -> pure r
    Left e -> throwError (f e)

modifyError :: (MonadError a m) => (a -> a) -> m c -> m c
modifyError f x = catchError x $ \e -> throwError (f e)
