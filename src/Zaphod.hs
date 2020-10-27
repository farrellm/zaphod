{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Zaphod where

import Options.Applicative
import qualified System.Console.Haskeline as Hl
import Text.Megaparsec (errorBundlePretty, runParser)
import Zaphod.Base
import Zaphod.Evaluator
import Zaphod.Parser (tokens)
import Zaphod.Types

data ZaphodOptions = ZaphodOptions
  { _path :: Maybe FilePath,
    _repl :: Bool,
    _cmd :: Maybe Text
  }
  deriving (Show)

type Zaphod l = StateT ZState (ExceptT (EvaluatorException l) IO)

emptyZState :: ZState
emptyZState =
  ZState
    { _environment = baseEnvironment
    }

printError :: (MonadIO m) => EvaluatorException Loc -> m ()
printError err =
  case err of
    (NoMatches z) ->
      putTextLn ("No implicit arguments available of type: " <> render z)
    (MultipleMatches z es) -> do
      putTextLn ("Multiple implicit arguments available of type: " <> render z)
      for_ es $ \e ->
        putTextLn ("- " <> render e)
    (InvalidParameters r) -> putTextLn ("Invalid parameters: " <> render r)
    (NotList r) -> putTextLn ("Expected a list, found: " <> render r)
    (BadBegin r) -> putTextLn ("Invalid 'begin': " <> render r)
    (NativeException l n) -> do
      print n
      printLocation l
    (CheckerException c) -> case c of
      TypeError a b l -> do
        putTextLn "Type mismatch: "
        putTextLn (render a <> " /= " <> render b)
        printLocation l
      ExistentialAlreadySolved t e u l -> do
        putTextLn
          ( "Existential already solved, setting " <> render e <> "=" <> render u
              <> " to "
              <> render t
          )
        printLocation l
      _ -> print (stripLocation c)
    (InvalidLambda r) -> do
      putTextLn ("Invalid lambda: " <> render r)
      printLocation (location r)
    (InvalidMacro r) -> do
      putTextLn ("Invalid macro: " <> render r)
      printLocation (location r)
  where
    printLocation (Just l) = putTextLn ("at " <> show l)
    printLocation Nothing = pass

evalText :: Text -> Zaphod Loc ()
evalText t =
  case runParser tokens "<cmd>" t of
    Left e -> putStrLn (errorBundlePretty e)
    Right rs -> traverse_ (evaluateTopLevel >=> putTextLn . render) rs

repl :: Maybe Text -> Zaphod Loc ()
repl _ = do
  z <- get
  z' <- Hl.runInputT Hl.defaultSettings (loop z)
  put z'
  where
    loop z = do
      minput <- Hl.getInputLine "> "
      case minput of
        Nothing -> pure z
        Just ":quit" -> pure z
        Just input ->
          case runParser tokens "<repl>" (toText input) of
            Left e -> do
              putStrLn (errorBundlePretty e)
              loop z
            Right rs -> do
              z' <- foldlM go z rs
              loop z'

    go z r = do
      res <- runExceptT $ runStateT (evaluateTopLevel r) z
      case res of
        Right (r', z') -> do
          putTextLn (render r')
          pure z'
        Left err -> do
          printError err
          pure z

runFile :: FilePath -> Zaphod Loc ()
runFile p = do
  t <- readFileText p
  zs <- case runParser tokens p t of
    Left e -> die (errorBundlePretty e)
    Right v -> pure v
  traverse_ evaluateTopLevel zs

zaphod :: IO ()
zaphod = do
  args <- execParser opts
  e <- runExceptT . evaluatingStateT emptyZState $ do
    runFile "base.zfd"
    runFile "prelude.zfd"
    case _path args of
      Just p -> do
        runFile p
        traverse_ evalText $ _cmd args
        when (_repl args) $ repl Nothing
      Nothing ->
        case _cmd args of
          Just c -> do
            evalText c
            when (_repl args) $ repl Nothing
          Nothing -> repl Nothing
  case e of
    Right () -> pass
    Left err -> printError err
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
