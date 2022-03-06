{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Context where

import qualified Data.Text as T
import Zaphod.Types.Class (Render (..))
import Zaphod.Types.Expr (Environment, Typed', ZType)
import Zaphod.Types.Wrapper (Existential, Universal, Variable)

data LookupResult
  = RSolved ZType
  | RUnsolved
  | RMissing
  deriving (Show)

data ContextEntry
  = CUnsolved Existential
  | CSolved Existential ZType
  | CMarker Existential
  | CUniversal Universal
  | CVariable Variable ZType
  | CEnvironment (Environment Typed')
  deriving (Show)

instance Render ContextEntry where
  render (CUnsolved a) = render a
  render (CSolved a b) = render a <> "=" <> render b
  render (CMarker a) = ">" <> render a
  render (CUniversal a) = render a
  render (CVariable a b) = render a <> ":" <> render b
  render (CEnvironment _) = "<env>"

newtype Context = Context [ContextEntry]
  deriving (Show)

instance Render Context where
  render (Context cs) = "Context [" <> T.intercalate ", " (render <$> cs) <> "]"

data Hole = Hole Existential [ContextEntry]
  deriving (Show)
