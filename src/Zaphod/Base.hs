{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base
  ( baseEnvironment,
    zBool,
    zTrue,
    zFalse,
  )
where

import Control.Concurrent.MVar (modifyMVar)
import qualified Data.Map as M
import System.IO.Unsafe (unsafePerformIO)
import Zaphod.Types

gensymRef :: MVar Int
{-# NOINLINE gensymRef #-}
gensymRef = unsafePerformIO (newMVar 0)

gensym :: IO Symbol
gensym = do
  r <- modifyMVar gensymRef $ \i -> pure (i + 1, i)
  pure $ Symbol ("#<gen>" <> show r)

data EvaluatorBug = TypeMismatch Typed Text
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

zBool :: ZType
zBool = zTuple1 (ZValue (ESymbol "Bool" ZSymbol))

zTrue :: Typed
zTrue = EPair (ESymbol "True" zBool) EUnit zBool

zFalse :: Typed
zFalse = EPair (ESymbol "False" zBool) EUnit zBool

baseEnvironment :: Environment
baseEnvironment =
  M.fromList
    [ -- Native values
      ("Top", EType ZTop),
      ("Symbol", EType ZSymbol),
      ("Type", EType (ZType 0)),
      -- Native functions
      ("zcons", ENative2 (Native2 $ \l r -> EType (ZPair (getType l) (getType r))) zZCons),
      --
      ("cons", ENative2 (Native2 $ \l r -> EPair l r (ZPair (exprType l) (exprType r))) zCons),
      ("fst", ENative1 (Native1 $ fst . getPair) zFst),
      ("snd", ENative1 (Native1 $ snd . getPair) zSnd),
      --
      ("is-nil", ENative1 (Native1 isNil) zPred),
      ("is-symbol", ENative1 (Native1 isSymbol) zPred),
      ("is-pair", ENative1 (Native1 isPair) zPred),
      ("symbol-eq", ENative2 (Native2 stripEq) zSymbolEq),
      ("top-eq", ENative2 (Native2 stripEq) zTopEq),
      ( "unsafe-gensym",
        ENativeIO (NativeIO (ESymbol <$> gensym <*> pure ZSymbol)) zUnsafeGensym
      ),
      -- Special forms
      ("if", ESpecial zIf),
      ("apply", ESpecial zApply),
      -- bypass type checker
      ("unsafe-coerce", ELambda' [Variable "x"] (ESymbol "x" zb) mempty zUnsafeCoerce)
    ]
  where
    zCons = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) (ZPair za zb)
    zFst = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) za
    zSnd = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) zb
    zZCons = ZFunction (zTuple2 (ZType 0) (ZType 0)) (ZType 0)
    zIf = ZForall a $ ZFunction (zTuple3 zBool za za) za
    zApply = ZForall a . ZForall b $ ZFunction (zTuple2 (ZFunction za zb) za) zb
    zUnsafeCoerce = ZForall a . ZForall b $ ZFunction (zTuple1 za) zb
    zUnsafeGensym = ZFunction ZUnit ZSymbol
    --
    zPred = ZForall a (ZFunction (zTuple1 za) zBool)
    zSymbolEq = ZFunction (zTuple2 ZSymbol ZSymbol) zBool
    zTopEq = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) zBool
    isNil EUnit = zTrue
    isNil _ = zFalse
    isSymbol (ESymbol _ _) = zTrue
    isSymbol _ = zFalse
    isPair (EPair _ _ _) = zTrue
    isPair _ = zFalse
    toZBool True = zTrue
    toZBool False = zFalse
    stripEq x y = toZBool (stripType x == stripType y)

getType :: Typed -> ZType
getType (EType z) = z
getType e = bug $ TypeMismatch e "Type"

getPair :: Typed -> (Typed, Typed)
getPair (EPair l r _) = (l, r)
getPair e = bug $ TypeMismatch e "Pair"
