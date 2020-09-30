{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Zaphod where

import Control.Exception (handle)
import Options.Applicative
import System.Console.Haskeline (InputT)
import qualified System.Console.Haskeline as Hl
import Text.Megaparsec (errorBundlePretty, parse)
import Zaphod.Base
import Zaphod.Evaluator
import Zaphod.Parser (tokens)
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

evalText :: Text -> StateT ZState IO ()
evalText t =
  case parse tokens "<cmd>" t of
    Left e -> do
      putStrLn (errorBundlePretty e)
    Right rs -> do
      rs' <- traverse evaluateTopLevel rs
      traverse_ (putTextLn . render) rs'

repl :: Maybe Text -> StateT ZState IO ()
repl _ = do
  z <- get
  z' <- Hl.runInputT Hl.defaultSettings (loop z)
  put z'
  where
    loop :: ZState -> InputT (StateT ZState IO) ZState
    loop z = do
      minput <- Hl.getInputLine "> "
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
      liftIO . handle (logBug z) $ do
        (r', z') <- runStateT (evaluateTopLevel r) z
        putTextLn (render r')
        pure z'
    logBug :: ZState -> Bug -> IO ZState
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
