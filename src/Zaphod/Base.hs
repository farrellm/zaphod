{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base where

import Zaphod.Types

baseContext :: Context
baseContext =
  Context []
  where

-- [ CVariable
--     (Variable "cons")
--     ( ZForall a . ZForall b $ ZFunction za (ZFunction zb zab)
--     ),
--   CVariable
--     (Variable "car")
--     (ZForall a . ZForall b $ ZFunction zab za),
--   CVariable
--     (Variable "cdr")
--     (ZForall a . ZForall b $ ZFunction zab zb)
-- ]
