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

data EvalContext l = EvalContext
  { _lclEnv :: Environment (Typed l),
    _gblEnv :: Environment (Typed l)
  }

makeEvalContext :: Environment (Typed l) -> EvalContext l
makeEvalContext gbl = EvalContext {_lclEnv = mempty, _gblEnv = gbl}

makeLenses ''EvalContext
