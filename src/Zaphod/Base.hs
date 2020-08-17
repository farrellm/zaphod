{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base (baseContext, baseEnvironment) where

import Zaphod.Types

baseContext :: Context
baseContext =
  Context
    [ CVariable
        (Variable "cons")
        ( ZForall a . ZForall b $
            ZFunction (zPair za zb) (ZPair za zb)
        )
    ]
  where
    a = Universal "a"
    b = Universal "b"
    za = ZUniversal a
    zb = ZUniversal b
    zPair l r = ZPair l $ ZPair r ZUnit

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

baseEnvironment :: Environment
baseEnvironment = mempty
