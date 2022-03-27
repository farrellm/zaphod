{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Context where

import qualified Data.Text as T
import Zaphod.Types.Class (Render (..))
import Zaphod.Types.Expr (Environment, Typed, ZType)
import Zaphod.Types.Wrapper (Existential, Universal, Variable)

data LookupResult l
  = RSolved (ZType (Typed l))
  | RUnsolved
  | RMissing
  deriving (Show)

data ContextEntry l
  = CUnsolved Existential
  | CSolved Existential (ZType (Typed l))
  | CMarker Existential
  | CUniversal Universal
  | CVariable Variable (ZType (Typed l))
  | CEnvironment (Environment (Typed l))
  deriving (Show)

instance Render (ContextEntry l) where
  render (CUnsolved a) = render a
  render (CSolved a b) = render a <> "=" <> render b
  render (CMarker a) = ">" <> render a
  render (CUniversal a) = render a
  render (CVariable a b) = render a <> ":" <> render b
  render (CEnvironment _) = "<env>"

newtype Context l = Context [ContextEntry l]
  deriving (Show)

instance Render (Context l) where
  render (Context cs) = "Context [" <> T.intercalate ", " (render <$> cs) <> "]"

data Hole l = Hole Existential [ContextEntry l]
  deriving (Show)
