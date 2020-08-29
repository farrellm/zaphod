{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Zaphod where

import Options.Applicative
import System.Console.Haskeline
import System.IO.Unsafe (unsafePerformIO)
import Text.Megaparsec (errorBundlePretty, parse)
import Zaphod.Base
import Zaphod.Checker
import Zaphod.Evaluator
import Zaphod.Parser (token, tokens)
import Zaphod.Types

data ZaphodBug
  = ZaphodBug
  deriving (Show)

data ZaphodOptions = ZaphodOptions
  { _path :: Maybe FilePath,
    _repl :: Bool,
    _cmd :: Maybe Text
  }
  deriving (Show)

instance Exception ZaphodBug

emptyZState :: ZState
emptyZState =
  ZState
    { _environment = baseEnvironment
    }

evalText :: forall m. (MonadState ZState m, MonadException m, MonadIO m) => Text -> m ()
evalText t =
  case parse token "<cmd>" t of
    Left e -> do
      putStrLn (errorBundlePretty e)
    Right r -> do
      r' <- evaluateTopLevel r
      putTextLn (render r')

repl :: forall m. (MonadState ZState m, MonadException m, MonadIO m) => Maybe Text -> m ()
repl _ = do
  z <- get
  z' <- runInputT defaultSettings (loop z)
  put z'
  where
    loop :: ZState -> InputT m ZState
    loop z = do
      minput <- getInputLine "> "
      case minput of
        Nothing -> pure z
        Just ":quit" -> pure z
        Just input -> do
          case parse tokens "<repl>" (toText input) of
            Left e -> do
              putStrLn (errorBundlePretty e)
              loop z
            Right rs -> do
              z' <- foldlM go z rs
              loop z'
    go z r =
      handle (logBug z) $ do
        (r', z') <- runStateT (evaluateTopLevel r) z
        putTextLn (render r')
        pure z'
    logBug :: ZState -> Bug -> InputT m ZState
    logBug z b = do
      print b
      pure z

runFile :: (MonadState ZState m, MonadIO m) => FilePath -> m ()
runFile p = do
  t <- readFileText p
  zs <- case parse tokens p t of
    Left e -> die (errorBundlePretty e)
    Right v -> pure v
  traverse_ evaluateTopLevel zs

zaphod :: IO ()
zaphod = do
  args <- execParser opts
  case _path args of
    Just p -> evaluatingStateT emptyZState $ do
      runFile "base.zfd"
      runFile "prelude.zfd"
      runFile p
      traverse_ evalText $ _cmd args
      when (_repl args) $ repl Nothing
    Nothing -> evaluatingStateT emptyZState $ do
      runFile "base.zfd"
      runFile "prelude.zfd"
      case _cmd args of
        Just c -> do
          evalText c
          when (_repl args) $ repl Nothing
        Nothing -> repl Nothing
  where
    opts =
      info
        (zaphodOptions <**> helper)
        ( fullDesc -- <> progDesc "Interpreter for Zaphod"
            <> header "zaphod - an interpreter for Zaphod"
        )

zaphodOptions :: Parser ZaphodOptions
zaphodOptions = do
  _repl <- switch (long "repl" <> help "drop into a REPL after running file")
  _path <- optional (strArgument (metavar "PATH" <> help "file to interpret"))
  _cmd <- optional $ strOption (short 'c' <> metavar "CMD" <> help "command to execute")
  pure ZaphodOptions {..}

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
  where
    print' :: (Render a) => a -> IO ()
    print' = putTextLn . render
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
    annLambda = "(: (lambda (x) x) (forall a (-> [a] a)))"
    annLambda2 = "(: (lambda (x) x) (-> [()] ()))"
    appLambda2' = "((lambda (x) (lambda (y) (cons x y))) ())"
    appLambda2'' = "(((lambda (x) (lambda (y) (cons x y))) ()) ())"
    appLambda2''' = "(((lambda (x) (lambda (y) [x y])) ()) ())"
    qSym = "(quote x)"
    qSym' = "'x"
    qNested = "(quote (x (a b) y z))"
    qNested' = "'(x (a b) y z)"
    top = "(: [() ()] Top)"
    ifNil = "(if (is-nil ()) (: '() Top) (: [()] Top))"
    ifNil' = "(if (is-nil [()]) (: '() Top) (: [()] Top))"
    -- lambda2p = "(\\x.(\\y.(x.y)))"
    parseTest t = unsafePerformIO $ case parse token "" t of
      Left e -> die (errorBundlePretty e)
      Right v -> pure v
    withZaphod = usingReader baseEnvironment . evaluatingStateT (emptyCheckerState baseEnvironment)
    analyzed a = withZaphod (analyzeUntyped $ parseTest a)
    synthesized a = withZaphod (synthesize <=< analyzeUntyped $ parseTest a)
    evaluated a = withZaphod (evaluate <=< synthesize <=< analyzeUntyped $ parseTest a)
