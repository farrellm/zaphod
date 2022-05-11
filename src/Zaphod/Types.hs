module Zaphod.Types
  ( module X,
    MonadChecker,
    MonadChecker',
    MonadEvaluator,
  )
where

import Zaphod.Types.Class as X
import Zaphod.Types.Context as X
import Zaphod.Types.Error as X
import Zaphod.Types.Expr as X
import Zaphod.Types.Location as X
import Zaphod.Types.Raw as X
import Zaphod.Types.State as X
import Zaphod.Types.Wrapper as X

type MonadChecker l m =
  ( MonadReader (ZState l) m,
    MonadState (CheckerState l) m,
    MonadError (CheckerException l) m,
    MonadIO m,
    Monoid l,
    Location l
  )

type MonadChecker' l m =
  ( MonadReader (ZState l) m,
    MonadState (CheckerState l) m,
    MonadError (CheckerException ()) m,
    MonadIO m,
    Monoid l,
    Location l
  )

type MonadEvaluator l m =
  ( MonadReader (ZState l) m,
    MonadError (EvaluatorException l) m,
    MonadIO m,
    Monoid l,
    Location l
  )
