{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types.State where

import Lens.Micro.Platform (makeLenses)
import Zaphod.Types.Context (Context (..), ContextEntry (CEnvironment))
import Zaphod.Types.Expr (Environment, Typed)

newtype ZState l = ZState
  { _environment :: Environment (Typed l)
  }
  deriving (Show)

makeLenses ''ZState

data CheckerState l = CheckerState
  { _context :: !(Context l),
    _existentialData :: !Char,
    _depth :: !Int
  }
  deriving (Show)

makeLenses ''CheckerState

emptyCheckerState :: Environment (Typed l) -> CheckerState l
emptyCheckerState env =
  CheckerState
    { _context = Context [CEnvironment env],
      _existentialData = 'α',
      _depth = 0
    }

freezeState :: (MonadState s m) => ReaderT s m a -> m a
freezeState x = runReaderT x =<< get
