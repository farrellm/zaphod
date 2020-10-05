{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Prelude
  ( module X,
    traceM',
  )
where

import Control.Monad.Except as X (MonadError, throwError)
import Relude as X
import Relude.Extra.Bifunctor as X (bimapF)

debug :: Bool
debug = False

traceM' :: Applicative f => Text -> f ()
traceM' x = when debug . traceM $ toString x
