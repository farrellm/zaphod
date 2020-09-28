{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Zaphod.Types.Class where

import qualified Data.Text as T

class Render a where
  render :: a -> Text

class MaybeList a where
  isList :: a -> Bool
  maybeList :: a -> Maybe [a]

class HasLocation a where
  type Loc a
  type UnitLoc a
  location :: a -> Loc a
  stripLocation :: a -> UnitLoc a
  setLocation :: Loc a -> UnitLoc a -> a

instance Render () where
  render () = "()"
  {-# INLINE render #-}

instance Render a => Render [a] where
  render xs = "(" <> T.intercalate " " (render <$> xs) <> ")"
  {-# INLINE render #-}

instance (Render a, Render b) => Render (a, b) where
  render (l, r) = "(" <> render l <> " . " <> render r <> ")"
  {-# INLINE render #-}
