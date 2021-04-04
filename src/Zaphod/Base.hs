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
zBool = ZValue (ESymbol "Bool" (ZType 0) :@ mempty)

zTrue :: (Monoid l) => Typed l
zTrue = ESymbol "True" zBool :@ mempty

zFalse :: (Monoid l) => Typed l
zFalse = ESymbol "False" zBool :@ mempty

baseEnvironment :: Environment (Typed ())
baseEnvironment =
  (Environment . M.fromList)
    [ -- Native values
      ("Any", EType ZAny :@ mempty),
      ("Symbol", EType ZSymbol :@ mempty),
      ("Type", EType (ZType 0) :@ mempty),
      -- Native functions
      ("zcons", ENative (Native (zcons . zUncurry2)) zZCons :@ mempty),
      --
      ("cons", ENative' (Native' (cons . zUncurry2)) zCons :@ mempty),
      ("fst", ENative' (Native' $ fmap fst . getPair "fst") zFst :@ mempty),
      ("snd", ENative' (Native' $ fmap snd . getPair "snd") zSnd :@ mempty),
      --
      ("is-nil", ENative (Native $ pure . isNil) zPred :@ mempty),
      ("is-symbol", ENative (Native $ pure . isSymbol) zPred :@ mempty),
      ("is-pair", ENative (Native $ pure . isPair) zPred :@ mempty),
      ("symbol-eq", ENative (Native (pure . stripEq . zUncurry2)) zSymbolEq :@ mempty),
      ("symbol-concat", ENative (Native (symbolConcat . zUncurry2)) zSymbolConcat :@ mempty),
      ("top-eq", ENative (Native (pure . stripEq . zUncurry2)) zAnyEq :@ mempty),
      ("unsafe-gensym", ENativeIO (NativeIO unsafeGensym) zUnsafeGensym :@ mempty),
      -- Special forms
      ("if", ESpecial zIf :@ mempty),
      ("apply", ESpecial zApply :@ mempty),
      -- bypass type checker
      ("unsafe-coerce", ENative' (Native' pure) zUnsafeCoerce :@ mempty)
    ]
  where
    zCons = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) (ZPair za zb)
    zFst = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) za
    zSnd = ZForall a . ZForall b $ ZFunction (zTuple1 (ZPair za zb)) zb
    zZCons = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) (ZType 0)
    zIf = ZForall a $ ZFunction (zTuple3 zBool za za) za
    zApply = ZForall a . ZForall b $ ZFunction (zTuple2 (ZFunction za zb) za) zb
    zUnsafeCoerce = ZForall a . ZForall b $ ZFunction (zTuple1 za) zb
    zUnsafeGensym = ZFunction ZUnit ZSymbol
    --
    zPred = ZForall a (ZFunction (zTuple1 za) zBool)
    zSymbolEq = ZFunction (zTuple2 ZSymbol ZSymbol) zBool
    zSymbolConcat = ZFunction (zTuple2 ZSymbol ZSymbol) ZSymbol
    zAnyEq = ZForall a . ZForall b $ ZFunction (zTuple2 za zb) zBool
    --
    zcons (l, r) = (:@ mempty) . EType <$> (ZPair <$> getType "zcons" l <*> getType "zcons" r)
    cons (l, r) = pure $ EPair l r (ZPair (exprType l) (exprType r)) :@ (location l <> location r)
    isNil (EUnit :@ _) = zTrue
    isNil _ = zFalse
    isSymbol (ESymbol {} :@ _) = zTrue
    isSymbol _ = zFalse
    isPair (EPair {} :@ _) = zTrue
    isPair _ = zFalse
    symbolConcat (x, y) = do
      s <- liftA2 (<>) (getSymbol "symbol-concat" x) (getSymbol "symbol-concat" y)
      pure (ESymbol s ZSymbol :@ mempty)
    toZBool True = zTrue
    toZBool False = zFalse
    stripEq (x, y) = toZBool (stripType x == stripType y)
    unsafeGensym = (:@ mempty) <$> (ESymbol <$> gensym <*> pure ZSymbol)

getType :: Text -> Typed l -> Either (NativeException l) ZType
getType _ (EType z :@ _) = pure z
getType n e = throwError $ TypeMismatch n e "Type"

getPair :: Text -> Typed l -> Either (NativeException l) (Typed l, Typed l)
getPair _ (EPair l r _ :@ _) = pure (l, r)
getPair n e = throwError $ TypeMismatch n e "Pair"

getSymbol :: Text -> Typed l -> Either (NativeException l) Symbol
getSymbol _ (ESymbol s _ :@ _) = pure s
getSymbol n e = throwError $ TypeMismatch n e "Symbol"

zUncurry2 :: Typed l -> (Typed l, Typed l)
zUncurry2 (EPair l (EPair r (EUnit :@ _) _ :@ _) _ :@ _) = (l, r)
zUncurry2 _ = bug Unreachable
