{-# LANGUAGE DeriveFunctor #-}

module Zaphod.Types.Error where

import Zaphod.Types.Expr (NativeException, Typed, Untyped, ZType)
import Zaphod.Types.Raw (Raw)
import Zaphod.Types.Wrapper (Existential, Variable)

data ZaphodBug
  = Unreachable
  | MissingExistential Existential
  deriving (Show)

instance Exception ZaphodBug

data EvaluatorException l
  = NoMatches ZType
  | MultipleMatches ZType [Typed ()]
  | InvalidParameters (Raw l)
  | NotList (Raw l)
  | BadBegin (Raw l)
  | NativeException NativeException
  | CheckerException (CheckerException l)
  deriving (Show, Functor)

data CheckerException l
  = ArgumentMissmatch [Variable] ZType
  | CannotApply ZType (Untyped l)
  | TypeError ZType ZType
  | UndefinedVariable Variable
  deriving (Show, Functor)
