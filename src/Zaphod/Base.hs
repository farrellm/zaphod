{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base (baseEnvironment) where

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

zTuple1 :: ZType -> ZType
zTuple1 x = ZPair x ZUnit

zTuple2 :: ZType -> ZType -> ZType
zTuple2 x y = ZPair x $ zTuple1 y

zTuple3 :: ZType -> ZType -> ZType -> ZType
zTuple3 x y z = ZPair x $ zTuple2 y z

baseEnvironment :: Environment
baseEnvironment =
  M.fromList
    [ -- Native values
      ("Top", EType ZTop),
      ("Type", EType (ZType 0)),
      -- Native functions
      ("cons", ENative2 (Native2 $ \l r -> EPair l r (ZPair (exprType l) (exprType r))) zCons),
      ("fst", ENative1 (Native1 $ fst . getPair) zFst),
      ("snd", ENative1 (Native1 $ snd . getPair) zSnd),
      --
      ("zcons", ENative2 (Native2 $ \l r -> EType (ZPair (getType l) (getType r))) zZCons),
      -- Special forms
      ("if-nil", ESpecial zIfNil),
      -- bypass type checker
      ("unsafe-coerce", ELambda' [Variable "x"] (ESymbol "x" zb) mempty zUnsafeCoerce)
    ]
  where
    zCons = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) (ZPair za zb)
    zFst = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) za
    zSnd = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) zb
    zZCons = ZFunction (zTuple2 (ZType 0) (ZType 0)) (ZType 0)
    zIfNil = ZForall a . ZForall b $ ZFunction (zTuple3 za zb zb) zb
    zUnsafeCoerce = ZForall a . ZForall b $ ZFunction (zTuple1 za) zb

getType :: Typed -> ZType
getType (EType z) = z
getType _ = bug TypeMismatch

getPair :: Typed -> (Typed, Typed)
getPair (EPair l r _) = (l, r)
getPair _ = bug TypeMismatch
