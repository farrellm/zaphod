{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Prelude
  ( module X,
    trace',
    traceM',
  )
where

import Control.Monad.Except as X (MonadError, throwError)
import Relude as X
import Relude.Extra.Bifunctor as X (bimapF)
import Relude.Extra.Enum as X (next, prev)

debug :: Bool
debug = False

trace' :: Text -> a -> a
trace' t = trace (toString t)

traceM' :: Applicative f => Text -> f ()
traceM' x = when debug . traceM $ toString x
