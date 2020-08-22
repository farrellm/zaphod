{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base (baseContext, baseEnvironment) where

import qualified Data.Map as M
import Zaphod.Types

data EvaluatorBug = TypeMismatch
  deriving (Show)

instance Exception EvaluatorBug

a :: Universal
a = Universal "a"

b :: Universal
b = Universal "b"

za :: ZType
za = ZUniversal a

zb :: ZType
zb = ZUniversal b

zPair :: ZType -> ZType -> ZType
zPair l r = ZPair l $ ZPair r ZUnit

zCons :: ZType
zCons = ZForall a . ZForall b $ ZFunction (zPair za zb) (ZPair za zb)

zZCons :: ZType
zZCons = ZFunction (zPair (ZType 0) (ZType 0)) (ZType 0)

zUnsafeCoerce :: ZType
zUnsafeCoerce = ZForall a . ZForall b $ ZFunction za zb

baseContext :: Context
baseContext =
  Context
    [ CVariable (Variable "cons") zCons,
      CVariable (Variable "zcons") zZCons,
      CVariable (Variable "unsafe-coerce") zUnsafeCoerce
    ]

-- [ CVariable
--     (Variable "car")
--     (ZForall a . ZForall b $ ZFunction zab za),
--   CVariable
--     (Variable "cdr")
--     (ZForall a . ZForall b $ ZFunction zab zb)
-- ]

baseEnvironment :: Environment
baseEnvironment =
  M.fromList
    [ ("cons", ENative2 (Native2 $ \l r -> EPair l r (ZPair (exprType l) (exprType r))) zCons),
      ("zcons", ENative2 (Native2 $ \l r -> EType (ZPair (getType l) (getType r))) zZCons),
      ("unsafe-coerce", ELambda (Variable "x") (ESymbol "x" zb) mempty zUnsafeCoerce)
    ]

getType :: Typed -> ZType
getType (EType z) = z
getType _ = bug TypeMismatch
