{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Zaphod where

import Options.Applicative
import qualified System.Console.Haskeline as Hl
import Text.Megaparsec (errorBundlePretty, runParser)
import Text.Megaparsec.Pos (sourcePosPretty)
import Zaphod.Base (baseContext, baseEnvironment)
import Zaphod.Evaluator (evaluateTopLevel)
import Zaphod.Parser (tokens)
import Zaphod.Types

data ZaphodOptions = ZaphodOptions
  { _path :: Maybe FilePath,
    _repl :: Bool,
    _cmd :: Maybe Text
  }
  deriving (Show)

type Zaphod = StateT (ZState (Maybe Loc)) (ExceptT (EvaluatorException (Maybe Loc)) IO)

emptyZState :: ZState (Maybe Loc)
emptyZState =
  ZState
    { _environment = embed <$> baseEnvironment,
      _envContext = embed <$> baseContext
    }

printError :: (MonadIO m) => EvaluatorException (Maybe Loc) -> m ()
printError err = do
  case err of
    NoMatches z l -> do
      printLocation l
      putTextLn ("No implicit arguments available of type: " <> render z)
    MultipleMatches z es l -> do
      printLocation l
      putTextLn ("Multiple implicit arguments available of type: " <> render z)
      for_ es $ \e ->
        putTextLn ("- " <> render e)
    InvalidParameters r -> putTextLn ("Invalid parameters: " <> render r)
    NotList r -> putTextLn ("Expected a list, found: " <> render r)
    BadBegin r -> putTextLn ("Invalid 'begin': " <> render r)
    NativeException n -> case n of
      TypeMismatch f x l t -> do
        printLocation l
        putTextLn
          ( "Runtime type mismatch in "
              <> f
              <> ", expecting "
              <> t
              <> " but got "
              <> render x
          )
    CallSite l err' -> do
      printLocation l
      printError err'
    CheckerException c -> case c of
      NotSubtype a b l -> do
        printLocation l
        putTextLn ("Not subtype: " <> render a <> " < " <> render b)
      TypeError a b l -> do
        printLocation l
        putTextLn ("Type mismatch: " <> render a <> " /= " <> render b)
      ExistentialAlreadySolved t e u l -> do
        printLocation l
        putTextLn
          ( "Existential already solved, setting "
              <> render e
              <> "="
              <> render u
              <> " to "
              <> render t
          )
      CannotApply t e l -> do
        printLocation l
        putTextLn ("Cannot apply type " <> render t <> " to value " <> render e)
      UndefinedVariable s l -> do
        printLocation l
        putTextLn ("Undefined variable: " <> render s)
      UnquoteOutsideQuasiquote e@(_ :# l) -> do
        printLocation l
        putTextLn ("Unquote outside of quasiquote: " <> render e)
      InvalidCasePattern p@(_ :# l) -> do
        printLocation l
        putTextLn ("Invalid case pattern: " <> render p)
      CheckerEvaluatorExc e -> do
        putTextLn "Evaluator exception in checker:"
        printError e
    InvalidLambda r@(_ :# l) -> do
      printLocation l
      putTextLn ("Invalid lambda: " <> render r)
    InvalidMacro r@(_ :# l) -> do
      printLocation l
      putTextLn ("Invalid macro: " <> render r)
    InvalidCase (_ :# l) -> do
      printLocation l
      putTextLn "Invalid case"
    PatternMatchingFailure v l -> do
      printLocation l
      putTextLn ("No matching pattern for value: " <> render v)
  where
    printLocation (Just (Loc b _)) = putStrLn (sourcePosPretty b <> ": error:")
    printLocation Nothing = pass

putRenderPairLn :: (Render a, Render b, MonadIO m) => (a, b) -> m ()
putRenderPairLn (a, b) = do
  putText (render a)
  putText " : "
  putTextLn (render b)

evalText :: Text -> Zaphod ()
evalText t =
  case runParser tokens "<cmd>" t of
    Left e -> putStrLn (errorBundlePretty e)
    Right rs -> traverse_ (evaluateTopLevel >=> putRenderPairLn) $ fmap Just <$> rs

repl :: Maybe Text -> Zaphod ()
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
              z' <- foldlM go z $ fmap Just <$> rs
              loop z'

    go z r = do
      res <- runExceptT $ runStateT (evaluateTopLevel r) z
      case res of
        Right (p, z') -> do
          putRenderPairLn p
          pure z'
        Left err -> do
          printError err
          pure z

runFile :: FilePath -> Zaphod ()
runFile p = do
  t <- readFileText p
  zs <- case runParser tokens p t of
    Left e -> die (errorBundlePretty e)
    Right v -> pure v
  traverse_ (evaluateTopLevel . fmap Just) zs

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
