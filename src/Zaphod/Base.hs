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
zBool = ZValue (ESymbol "Bool" (ZType 0) :@ ())

zTrue :: Typed ()
zTrue = ESymbol "True" zBool :@ ()

zFalse :: Typed ()
zFalse = ESymbol "False" zBool :@ ()

baseEnvironment :: Environment
baseEnvironment =
  M.fromList
    [ -- Native values
      ("Any", EType ZAny :@ ()),
      ("Symbol", EType ZSymbol :@ ()),
      ("Type", EType (ZType 0) :@ ()),
      -- Native functions
      ("zcons", ENative2 (Native2 zcons) zZCons :@ ()),
      --
      ("cons", ENative2 (Native2 $ \l r -> pure $ cons l r) zCons :@ ()),
      ("fst", ENative1 (Native1 $ fmap fst . getPair "fst") zFst :@ ()),
      ("snd", ENative1 (Native1 $ fmap snd . getPair "snd") zSnd :@ ()),
      --
      ("is-nil", ENative1 (Native1 $ pure . isNil) zPred :@ ()),
      ("is-symbol", ENative1 (Native1 $ pure . isSymbol) zPred :@ ()),
      ("is-pair", ENative1 (Native1 $ pure . isPair) zPred :@ ()),
      ("symbol-eq", ENative2 (Native2 $ \x y -> pure $ stripEq x y) zSymbolEq :@ ()),
      ("symbol-concat", ENative2 (Native2 symbolConcat) zSymbolConcat :@ ()),
      ("top-eq", ENative2 (Native2 $ \x y -> pure $ stripEq x y) zAnyEq :@ ()),
      ("unsafe-gensym", ENativeIO (NativeIO unsafeGensym) zUnsafeGensym :@ ()),
      -- Special forms
      ("if", ESpecial zIf :@ ()),
      ("apply", ESpecial zApply :@ ()),
      -- bypass type checker
      ("unsafe-coerce", ENative1 (Native1 pure) zUnsafeCoerce :@ ())
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
    zcons l r = (:@ ()) . EType <$> (ZPair <$> getType "zcons" l <*> getType "zcons" r)
    cons l r = EPair l r (ZPair (exprType l) (exprType r)) :@ ()
    isNil (EUnit :@ _) = zTrue
    isNil _ = zFalse
    isSymbol (ESymbol {} :@ _) = zTrue
    isSymbol _ = zFalse
    isPair (EPair {} :@ _) = zTrue
    isPair _ = zFalse
    symbolConcat x y = do
      s <- liftA2 (<>) (getSymbol "symbol-concat" x) (getSymbol "symbol-concat" y)
      pure (ESymbol s ZSymbol :@ ())
    toZBool True = zTrue
    toZBool False = zFalse
    stripEq x y = toZBool (stripType x == stripType y)
    unsafeGensym = (:@ ()) <$> (ESymbol <$> gensym <*> pure ZSymbol)

getType :: Text -> Typed l -> Either NativeException ZType
getType _ (EType z :@ _) = pure z
getType n e = throwError $ TypeMismatch n (stripLocation e) "Type"

getPair :: Text -> Typed l -> Either NativeException (Typed l, Typed l)
getPair _ (EPair l r _ :@ _) = pure (l, r)
getPair n e = throwError $ TypeMismatch n (stripLocation e) "Pair"

getSymbol :: Text -> Typed l -> Either NativeException Symbol
getSymbol _ (ESymbol s _ :@ _) = pure s
getSymbol n e = throwError $ TypeMismatch n (stripLocation e) "Symbol"
