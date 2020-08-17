{-# LANGUAGE OverloadedStrings #-}

module Zaphod where

import System.IO.Unsafe (unsafePerformIO)
import Text.Megaparsec (errorBundlePretty, parse)
import Zaphod.Base
import Zaphod.Checker
import Zaphod.Evaluator
import Zaphod.Parser
import Zaphod.Types

data ZaphodBug
  = InvalidType Untyped
  | InvalidParameters Untyped
  deriving (Show)

instance Exception ZaphodBug

emptyZState :: ZState
emptyZState =
  ZState
    { _context = baseContext,
      _environment = baseEnvironment,
      _existentialData = 'α'
    }

analyzeType :: Untyped -> ZType
analyzeType (EType (ZType n)) = ZType (n + 1)
analyzeType (EType _) = ZType 0
analyzeType EUnit = ZUnit
analyzeType (ESymbol x ()) = ZUniversal (Universal x)
analyzeType (EPair "forall" (EPair (ESymbol u ()) (EPair z EUnit ()) ()) ()) =
  ZForall (Universal u) (analyzeType z)
analyzeType (EPair "->" (EPair a (EPair b EUnit ()) ()) ()) =
  ZFunction (analyzeType a) (analyzeType b)
analyzeType t =
  case maybeList t of
    Just ts -> makeZList (analyzeType <$> ts)
    Nothing -> bug (InvalidType t)

analyzeUntyped :: Untyped -> Untyped
analyzeUntyped
  ( EPair
      "lambda"
      (EPair (ESymbol x ()) (EPair e EUnit ()) ())
      ()
    ) = ELambda (Variable x) (analyzeUntyped e) mempty ()
analyzeUntyped (EPair "lambda" (EPair xs (EPair e EUnit ()) ()) ()) =
  case mkParams xs of
    Just ps -> ELambda' ps (analyzeUntyped e) mempty ()
    Nothing -> bug (InvalidParameters xs)
  where
    mkParams :: Untyped -> Maybe [Variable]
    mkParams EUnit = Just []
    mkParams (EPair (ESymbol z ()) zs ()) = (Variable z :) <$> mkParams zs
    mkParams _ = Nothing
analyzeUntyped (EPair ":" (EPair e (EPair t EUnit ()) ()) ()) =
  EAnnotation (analyzeUntyped e) (analyzeType t)
analyzeUntyped (EPair "quote" (EPair x EUnit ()) ()) = EQuote x ()
analyzeUntyped (ELambda x e n ()) = ELambda x (analyzeUntyped e) n ()
analyzeUntyped (EPair a b ()) =
  case maybeList b of
    Just xs -> EApply (analyzeUntyped a) (analyzeUntyped <$> xs) ()
    Nothing -> EPair (analyzeUntyped a) (analyzeUntyped b) ()
analyzeUntyped (EAnnotation e t) = EAnnotation (analyzeUntyped e) t
analyzeUntyped a = a

test :: IO ()
test = do
  print' (parseTest unit)
  print' (parseTest pair)
  print' (parseTest lambda)
  print' (parseTest lambdaU)
  -- print' (parseTest lambda2)
  print' (parseTest lambda2')
  print' (parseTest lambda2'')
  print' (parseTest lambda3)
  print' (parseTest appLambda)
  print' (parseTest annUnit)
  print' (parseTest annLambda)
  print' (parseTest appLambda2')
  print' (parseTest appLambda2'')
  print' (parseTest qSym)
  print' (parseTest qSym')
  print' (parseTest qNested)
  print' (parseTest qNested')
  putStrLn "-"
  print' (analyzed unit)
  print' (analyzed pair)
  print' (analyzed lambda)
  print' (analyzed lambdaU)
  -- print' (analyzed lambda2)
  print' (analyzed lambda2')
  print' (analyzed lambda2'')
  print' (analyzed lambda3)
  print' (analyzed appLambda)
  print' (analyzed appLambda2)
  print' (analyzed annUnit)
  print' (analyzed annLambda)
  print' (analyzed appLambda2')
  print' (analyzed appLambda2'')
  print' (analyzed qSym)
  print' (analyzed qSym')
  print' (analyzed qNested)
  print' (analyzed qNested')
  putStrLn "-"
  print' (synthesized unit)
  print' (synthesized lambda)
  print' (synthesized lambdaU)
  -- print' (synthesized lambda2)
  print' (synthesized lambda2')
  print' (synthesized lambda2'')
  print' (synthesized lambda3)
  print' (synthesized annUnit)
  print' (synthesized appLambda)
  print' (synthesized appLambda2)
  print' (synthesized annLambda)
  print' (synthesized appLambda2')
  print' (synthesized appLambda2'')
  print' (synthesized qSym)
  putStrLn "-"
  print' (evaluated appLambda)
  print' (evaluated appLambda2)
  print' (evaluated appLambda2)
  print' (evaluated appLambda2')
  print' (evaluated appLambda2'')
  print' (evaluated qSym)
  print' (evaluated qSym')
  print' (evaluated qNested)
  print' (evaluated qNested')
  where
    print' :: (Render a) => a -> IO ()
    print' = putStrLn . toString . render
    --
    unit = "()"
    pair = "(().())"
    lambda = "(lambda (x) x)"
    lambdaU = "(lambda (x) ())"
    -- lambda2 = "(lambda x (lambda y x))"
    lambda2' = "(lambda (x) (lambda (y) x))"
    lambda2'' = "(lambda (x) (lambda (y) (cons x y)))"
    lambda3 = "(lambda (x y) x)"
    appLambda = "((lambda (x) x) ())"
    appLambda2 = "((lambda (x y) x) () ())"
    annUnit = "(: () ())"
    annLambda = "(: (lambda (x) x) (forall a (-> (a) a)))"
    appLambda2' = "((lambda (x) (lambda (y) (cons x y))) ())"
    appLambda2'' = "(((lambda (x) (lambda (y) (cons x y))) ()) ())"
    qSym = "(quote x)"
    qSym' = "'x"
    qNested = "(quote (x (a b) y z))"
    qNested' = "'(x (a b) y z)"
    -- lambda2p = "(\\x.(\\y.(x.y)))"
    parseTest t = unsafePerformIO $ case parse token "" t of
      Left e -> die (errorBundlePretty e)
      Right v -> pure v
    analyzed a = analyzeUntyped $ parseTest a
    synthesized a = evalState (synthesize $ analyzed a) emptyZState
    evaluated a = evalState (evaluate =<< synthesize (analyzed a)) emptyZState
