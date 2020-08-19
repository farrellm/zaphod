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
  = InvalidType Raw
  | InvalidParameters Raw
  deriving (Show)

instance Exception ZaphodBug

emptyZState :: ZState
emptyZState =
  ZState
    { _context = baseContext,
      _environment = baseEnvironment,
      _existentialData = 'α'
    }

analyzeType :: Raw -> ZType
analyzeType RUnit = ZUnit
analyzeType (RSymbol x) = ZUniversal (Universal x)
analyzeType (RPair "forall" (RPair (RSymbol u) (RPair z RUnit))) =
  ZForall (Universal u) (analyzeType z)
analyzeType (RPair "->" (RPair a (RPair b RUnit))) =
  ZFunction (analyzeType a) (analyzeType b)
analyzeType t =
  case maybeList t of
    Just ts -> fromList' (analyzeType <$> ts)
    Nothing -> bug (InvalidType t)

analyzeQuoted :: Raw -> Untyped
analyzeQuoted RUnit = EUnit
analyzeQuoted (RSymbol s) = ESymbol s ()
analyzeQuoted (RPair l r) = EPair (analyzeQuoted l) (analyzeQuoted r) ()

analyzeUntyped :: Raw -> Untyped
analyzeUntyped RUnit = EUnit
analyzeUntyped (RSymbol s) = ESymbol s ()
analyzeUntyped
  ( RPair
      "lambda"
      (RPair (RSymbol x) (RPair e RUnit))
    ) = ELambda (Variable x) (analyzeUntyped e) mempty ()
analyzeUntyped (RPair "lambda" (RPair xs (RPair e RUnit))) =
  case mkParams xs of
    Just ps -> ELambda' ps (analyzeUntyped e) mempty ()
    Nothing -> bug (InvalidParameters xs)
  where
    mkParams :: Raw -> Maybe [Variable]
    mkParams RUnit = Just []
    mkParams (RPair (RSymbol z) zs) = (Variable z :) <$> mkParams zs
    mkParams _ = Nothing
analyzeUntyped (RPair ":" (RPair e (RPair t RUnit))) =
  EAnnotation (analyzeUntyped e) (analyzeType t)
analyzeUntyped (RPair "quote" (RPair x RUnit)) = EQuote (analyzeQuoted x) ()
analyzeUntyped (RPair a b) =
  case maybeList b of
    Just xs -> EApply (analyzeUntyped a) (analyzeUntyped <$> xs) ()
    Nothing -> EPair (analyzeUntyped a) (analyzeUntyped b) ()

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
