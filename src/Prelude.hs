{-# OPTIONS_GHC -fno-warn-deprecations #-}

module Prelude
  ( module X,
    traceM',
  )
where

import Relude as X

debug :: Bool
debug = False

traceM' :: Applicative f => Text -> f ()
traceM' x = when debug . traceM $ toString x
