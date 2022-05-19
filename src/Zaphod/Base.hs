{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Base
  ( baseEnvironment,
    baseContext,
  )
where

import Control.Concurrent.MVar (modifyMVar)
import qualified Data.Map as M
import System.IO.Unsafe (unsafePerformIO)
import Zaphod.Types hiding (getSymbol)

gensymRef :: MVar Int
{-# NOINLINE gensymRef #-}
gensymRef = unsafePerformIO (newMVar 0)

gensym :: IO Symbol
gensym = do
  r <- modifyMVar gensymRef $ \i -> pure (i + 1, i)
  pure $ Symbol ("#<gen>" <> show r)

a :: Universal
a = Universal "a"

b :: Universal
b = Universal "b"

za :: ZType Typed'
za = ZUniversal a

zb :: ZType Typed'
zb = ZUniversal b

zTuple1 :: ZType Typed' -> ZType Typed'
zTuple1 x = ZPair x ZUnit

zTuple2 :: ZType Typed' -> ZType Typed' -> ZType Typed'
zTuple2 x y = ZPair x $ zTuple1 y

zBool :: ZType Typed'
zBool = ZValue (ESymbol "Bool" :$ ZSymbol)

zTrue :: Untyped'
zTrue = LocU $ ESymbol "True"

zFalse :: Untyped'
zFalse = LocU $ ESymbol "False"

baseEnvironment :: Environment Untyped'
baseEnvironment =
  (Environment . M.fromList)
    [ -- Native values
      ("Any", LocU (EType ZAny)),
      ("Symbol", LocU (EType ZSymbol)),
      ("Type", LocU (EType (ZType 0))),
      -- Native functions
      ("cons", LocU (ENative' (Native' (pure . cons . zUncurry2)))),
      ("fst", LocU (ENative' (Native' (fmap fst . getPair "fst")))),
      ("snd", LocU (ENative' (Native' (fmap snd . getPair "snd")))),
      --
      ("is-nil", LocU (ENative (Native (pure . isNil)))),
      ("is-symbol", LocU (ENative (Native (pure . isSymbol)))),
      ("is-pair", LocU (ENative (Native (pure . isPair)))),
      ("symbol-eq", LocU (ENative (Native (pure . toZBool . topEq . zUncurry2')))),
      ("symbol-concat", LocU (ENative (Native (symbolConcat . zUncurry2')))),
      ("top-eq", LocU (ENative (Native (pure . toZBool . topEq . zUncurry2')))),
      ("unsafe-gensym", LocU (ENativeIO (NativeIO unsafeGensym))),
      ("promote", LocU (ENative (Native (pure . promote)))),
      -- Special forms
      ("apply", LocU ESpecial),
      ("capture", LocU (ENative (Native (pure . capture)))),
      -- bypass type checker
      ("unsafe-coerce", LocU (ENative' (Native' pure)))
    ]
  where
    cons (l@(_ :# ll), r@(_ :# lr)) = EPair l r :# (ll <> lr)

    isNil (LocU EUnit) = zTrue
    isNil _ = zFalse

    isSymbol (LocU ESymbol {}) = zTrue
    isSymbol (LocU ETsSymbol {}) = zTrue
    isSymbol _ = zFalse

    isPair (LocU EPair {}) = zTrue
    isPair _ = zFalse

    symbolConcat (x, y) = do
      s <- liftA2 (<>) (getSymbol "symbol-concat" x) (getSymbol "symbol-concat" y)
      pure (LocU $ ESymbol s)

    toZBool True = zTrue
    toZBool False = zFalse

    topEq (LocU EUnit, LocU EUnit) = True
    topEq (LocU (ESymbol x), LocU (ESymbol y)) = x == y
    topEq (LocU (ESymbol x), LocU (ETsSymbol y _)) = x == y
    topEq (LocU (ETsSymbol x _), LocU (ESymbol y)) = x == y
    topEq (LocU (ETsSymbol x _), LocU (ETsSymbol y _)) = x == y
    topEq (LocU (EPair x1 x2), LocU (EPair y1 y2)) = topEq (x1, y1) && topEq (x2, y2)
    topEq _ = False

    unsafeGensym = LocU . flip ETsSymbol 0 <$> gensym

    capture (LocU (ESymbol s)) = LocU (ETsSymbol s 0)
    capture _ = bug Unreachable

    promote x = LocU $ EType (ZValue x)

baseContext :: Environment (ZType Typed')
baseContext =
  (Environment . M.fromList)
    [ -- Native values
      ("Any", ZType 0),
      ("Symbol", ZType 0),
      ("Type", ZType 1),
      -- Native functions
      ("cons", zCons),
      ("fst", zFst),
      ("snd", zSnd),
      --
      ("is-nil", zPred),
      ("is-symbol", zPred),
      ("is-pair", zPred),
      ("symbol-eq", zSymbolEq),
      ("symbol-concat", zSymbolConcat),
      ("top-eq", zAnyEq),
      ("unsafe-gensym", zUnsafeGensym),
      ("promote", zPromote),
      -- Special forms
      ("apply", zApply),
      ("capture", zCapture),
      -- bypass type checker
      ("unsafe-coerce", zUnsafeCoerce),
      -- bootstrapping
      ("True", zBool)
    ]
  where
    zCons = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) (ZPair za zb)
    zFst = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) za
    zSnd = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) zb
    zApply = ZForall a . ZForall b $ ZFunction (zTuple2 (ZFunction za zb) za) zb
    zCapture = ZFunction (zTuple1 ZSymbol) ZSymbol
    zUnsafeCoerce = ZForall a . ZForall b $ ZFunction (zTuple1 za) zb
    zUnsafeGensym = ZFunction ZUnit ZSymbol
    zPromote = ZForall a $ ZFunction za (ZType 0)
    --
    zPred = ZForall a (ZFunction (zTuple1 za) zBool)
    zSymbolEq = ZFunction (zTuple2 ZSymbol ZSymbol) zBool
    zSymbolConcat = ZFunction (zTuple2 ZSymbol ZSymbol) ZSymbol
    zAnyEq = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) zBool

getPair :: Text -> Untyped l -> Either (NativeException ()) (Untyped l, Untyped l)
getPair _ (EPair l r :# _) = pure (l, r)
getPair n e = throwError $ TypeMismatch n (project e) () "Pair"

getSymbol :: Text -> Untyped' -> Either (NativeException ()) Symbol
getSymbol _ (LocU (ESymbol s)) = pure s
getSymbol _ (LocU (ETsSymbol s 0)) = pure s
getSymbol n e = throwError $ TypeMismatch n e () "Symbol"

zUncurry2 :: Untyped l -> (Untyped l, Untyped l)
zUncurry2 e
  | EPair l e' :# _ <- e,
    EPair r e'' :# _ <- e',
    EUnit :# _ <- e'' =
      (l, r)
zUncurry2 _ = bug Unreachable

zUncurry2' :: Untyped' -> (Untyped', Untyped')
zUncurry2' e
  | LocU (EPair l e') <- e,
    LocU (EPair r e'') <- e',
    LocU EUnit <- e'' =
      (l, r)
zUncurry2' _ = bug Unreachable
