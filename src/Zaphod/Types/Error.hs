{-# LANGUAGE DeriveFunctor #-}

module Zaphod.Types.Error where

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
  = NoMatches ZType
  | MultipleMatches ZType [Typed ()]
  | InvalidParameters (Raw l)
  | NotList (Raw l)
  | BadBegin (Raw l)
  | NativeException l NativeException
  | CheckerException (CheckerException l)
  | InvalidLambda (Raw l)
  | InvalidMacro (Raw l)
  deriving (Show, Functor)

data CheckerException l
  = ArgumentMissmatch [Variable] ZType
  | CannotApply ZType (Untyped l)
  | TypeError ZType ZType l
  | NotSubtype ZType ZType l
  | UndefinedVariable Variable
  | ExistentialAlreadySolved ZType Existential ZType l
  deriving (Show, Functor)
