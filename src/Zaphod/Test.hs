{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Test where

import Text.Megaparsec (errorBundlePretty, parse)
import Zaphod
import Zaphod.Checker
import Zaphod.Evaluator
import Zaphod.Parser (token)
import Zaphod.Types

test :: IO ()
test = do
  res <- runExceptT . evaluatingStateT emptyZState $ do
    runFile "base.zfd"
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
    print' (parseTest annUnit')
    print' (parseTest annLambda)
    print' (parseTest annLambda2)
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
    print' (analyzed annUnit')
    print' (analyzed annLambda)
    print' (analyzed annLambda2)
    print' (analyzed appLambda2')
    print' (analyzed appLambda2'')
    print' (analyzed appLambda2''')
    print' (analyzed qSym)
    print' (analyzed qSym')
    print' (analyzed qNested)
    print' (analyzed qNested')
    print' (analyzed ifNil)
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
    print' (synthesized annLambda2)
    print' (synthesized appLambda2')
    print' (synthesized appLambda2'')
    print' (synthesized appLambda2''')
    print' (synthesized qSym)
    print' (synthesized top)
    print' (synthesized ifNil)
    print' (synthesized car)
    putStrLn "-"
    print' (evaluated annLambda2)
    print' (evaluated appLambda)
    print' (evaluated appLambda2)
    print' (evaluated appLambda2)
    print' (evaluated appLambda2')
    print' (evaluated appLambda2'')
    print' (evaluated appLambda2''')
    print' (evaluated qSym)
    print' (evaluated qSym')
    print' (evaluated qNested)
    print' (evaluated qNested')
    print' (evaluated top)
    print' (evaluated ifNil)
    print' (evaluated ifNil')
    print' (evaluated car)
  case res of
    Right () -> pass
    Left err -> print err
  where
    print' ioA = putTextLn . render =<< ioA
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
    annUnit' = "(: () [])"
    annLambda = "(: (lambda (x) x) (forall (a) (-> [a] a)))"
    annLambda2 = "(: (lambda (x) x) (-> [()] ()))"
    appLambda2' = "((lambda (x) (lambda (y) (cons x y))) ())"
    appLambda2'' = "(((lambda (x) (lambda (y) (cons x y))) ()) ())"
    appLambda2''' = "(((lambda (x) (lambda (y) [x y])) ()) ())"
    qSym = "(quote x)"
    qSym' = "'x"
    qNested = "(quote (x (a b) y z))"
    qNested' = "'(x (a b) y z)"
    top = "(: [() ()] Any)"
    ifNil = "(if (is-nil ()) (: '() Any) (: [()] Any))"
    ifNil' = "(if (is-nil [()]) (: '() Any) (: [()] Any))"
    car = "(car '(a b c))"
    -- lambda2p = "(\\x.(\\y.(x.y)))"
    parseTest t = case parse token "" t of
      Left e -> die (errorBundlePretty e)
      Right v -> pure v
    withZaphod a = do
      env <- _environment <$> get
      usingReaderT env $
        evaluatingStateT (emptyCheckerState env) a
    analyzed a =
      withZaphod
        ( analyzeUntyped
            =<< macroExpand
            =<< parseTest a
        )
    synthesized a =
      withZaphod
        ( liftChecker synthesize
            =<< analyzeUntyped
            =<< macroExpand
            =<< parseTest a
        )
    evaluated a =
      withZaphod
        ( evaluate
            =<< liftChecker synthesize
            =<< analyzeUntyped
            =<< macroExpand
            =<< parseTest a
        )
