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
import Relude.Extra.Bifunctor (secondF)
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
zBool = ZValue (LocU $ ESymbol "Bool" (ZType 0))

zTrue :: Typed ()
zTrue = ESymbol "True" zBool :@@ mempty

zFalse :: Typed ()
zFalse = ESymbol "False" zBool :@@ mempty

baseEnvironment :: Environment (Typed ())
baseEnvironment =
  (Environment . M.fromList . secondF LocU)
    [ -- Native values
      ("Any", EType ZAny),
      ("Symbol", EType ZSymbol),
      ("Type", EType (ZType 0)),
      -- Native functions
      ("zcons", ENative (Native (zcons . zUncurry2)) zZCons),
      --
      ("cons", ENative' (Native' (cons . zUncurry2)) zCons),
      ("fst", ENative' (Native' $ fmap fst . getPair "fst") zFst),
      ("snd", ENative' (Native' $ fmap snd . getPair "snd") zSnd),
      --
      ("is-nil", ENative (Native $ pure . isNil) zPred),
      ("is-symbol", ENative (Native $ pure . isSymbol) zPred),
      ("is-pair", ENative (Native $ pure . isPair) zPred),
      ("symbol-eq", ENative (Native (pure . stripEq . zUncurry2)) zSymbolEq),
      ("symbol-concat", ENative (Native (symbolConcat . zUncurry2)) zSymbolConcat),
      ("top-eq", ENative (Native (pure . stripEq . zUncurry2)) zAnyEq),
      ("unsafe-gensym", ENativeIO (NativeIO unsafeGensym) zUnsafeGensym),
      -- Special forms
      ("if", ESpecial zIf),
      ("apply", ESpecial zApply),
      -- bypass type checker
      ("unsafe-coerce", ENative' (Native' pure) zUnsafeCoerce)
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
    zcons (l, r) = LocU . EType <$> (ZPair <$> getType "zcons" l <*> getType "zcons" r)
    cons (l, r) = pure $ EPair l r (ZPair (exprType l) (exprType r)) :@@ (location l <> location r)
    isNil (EUnit :@@ _) = zTrue
    isNil _ = zFalse
    isSymbol (ESymbol {} :@@ _) = zTrue
    isSymbol _ = zFalse
    isPair (EPair {} :@@ _) = zTrue
    isPair _ = zFalse
    symbolConcat (x, y) = do
      s <- liftA2 (<>) (getSymbol "symbol-concat" x) (getSymbol "symbol-concat" y)
      pure (ESymbol s ZSymbol :@@ mempty)
    toZBool True = zTrue
    toZBool False = zFalse
    stripEq (x, y) = toZBool (void x == void y)
    unsafeGensym = LocU <$> (ESymbol <$> gensym <*> pure ZSymbol)

getType :: (LocationExpr (Typed l) ZType l) => Text -> Typed l -> Either (NativeException l) ZType
getType _ e | EType z <- value e = pure z
getType n e = throwError $ TypeMismatch n (stripLocation e) (location e) "Type"

getPair :: (CTyped l) => Text -> Typed l -> Either (NativeException l) (Typed l, Typed l)
getPair _ (EPair l r _ :@@ _) = pure (l, r)
getPair n e = throwError $ TypeMismatch n (stripLocation e) (location e) "Pair"

getSymbol :: Text -> Typed () -> Either (NativeException ()) Symbol
getSymbol _ (LocU (ESymbol s _)) = pure s
getSymbol n e = throwError $ TypeMismatch n (stripLocation e) (location e) "Symbol"

zUncurry2 :: (CTyped l) => Typed l -> (Typed l, Typed l)
zUncurry2 e
  | EPair l e' _ <- value e,
    EPair r e'' _ <- value e',
    EUnit <- value e'' =
    (l, r)
zUncurry2 _ = bug Unreachable
