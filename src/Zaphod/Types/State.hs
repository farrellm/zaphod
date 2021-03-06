{-# LANGUAGE TemplateHaskell #-}

module Zaphod.Types.State where

import Lens.Micro.TH (makeLenses)
import Zaphod.Types.Context
import Zaphod.Types.Expr (Environment, Typed)

newtype ZState = ZState
  { _environment :: Environment (Typed ())
  }
  deriving (Show)

makeLenses ''ZState

data CheckerState = CheckerState
  { _context :: !Context,
    _existentialData :: !Char,
    _depth :: !Int
  }
  deriving (Show)

makeLenses ''CheckerState

emptyCheckerState :: Environment (Typed ()) -> CheckerState
emptyCheckerState env =
  CheckerState
    { _context = Context [CEnvironment env],
      _existentialData = 'α',
      _depth = 0
    }
