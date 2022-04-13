{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Prelude
  ( module X,
    trace',
    traceM',
    debug,
    debugM,
  )
where

import Control.Monad.Except as X (MonadError, throwError)
import Relude as X
import Relude.Extra.Bifunctor as X (bimapF)
import Relude.Extra.Enum as X (next, prev)

enableDebug :: Bool
enableDebug = False

trace' :: Text -> a -> a
trace' t = trace (toString t)

traceM' :: Applicative f => Text -> f ()
traceM' x = traceM $ toString x

debug :: Text -> a -> a
debug t =
  if enableDebug
    then trace (toString t)
    else id

debugM :: Applicative f => Text -> f ()
debugM x = when enableDebug $ traceM' x
