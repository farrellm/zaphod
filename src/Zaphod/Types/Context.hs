{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Context where

import qualified Data.Text as T
import Zaphod.Types.Class
import Zaphod.Types.Expr
import Zaphod.Types.Wrapper

data LookupResult
  = RSolved ZType
  | RUnsolved
  | RMissing
  deriving (Show)

data ContextEntry l
  = CUnsolved Existential
  | CSolved Existential ZType
  | CMarker Existential
  | CUniversal Universal
  | CVariable Variable ZType
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
