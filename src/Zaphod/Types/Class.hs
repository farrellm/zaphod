{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Class where

import qualified Data.Text as T
import Relude.Extra.Bifunctor (firstF)

class Render a where
  render :: a -> Text

class MaybeList a where
  isList :: a -> Bool
  maybeList :: a -> Maybe [a]

class Magma a where
  (><) :: a -> a -> a

infixr 6 ><

class Semigroup l => Location l where
  locBegin :: l -> l
  locEnd :: l -> l

instance Render () where
  render () = "()"

instance (Render a) => Render [a] where
  render xs = "(" <> T.intercalate " " (render <$> xs) <> ")"

instance (Render a) => Render (NonEmpty a) where
  render xs = "(" <> T.intercalate " " (render <$> toList xs) <> ")"

instance (Render a, Render b) => Render (a, b) where
  render (l, r) = "(" <> render l <> " . " <> render r <> ")"

instance (Render a, Render b, Render c) => Render (a, b, c) where
  render (a, b, c) = "(" <> render a <> " . " <> render b <> " . " <> render c <> ")"

instance Location () where
  locBegin () = ()
  locEnd () = ()

instance (Location l) => Location (Maybe l) where
  locBegin = (locBegin <$>)
  locEnd = (locEnd <$>)

class Injection a b where
  embed :: a -> b

class Projection a b where
  project :: a -> b

instance (Injection a b, Functor f) => Injection (f a) (f b) where
  {-# INLINE embed #-}
  embed = fmap embed

instance (Projection a b, Functor f) => Projection (f a) (f b) where
  {-# INLINE project #-}
  project = fmap project

instance Projection (a, b) b where
  {-# INLINE project #-}
  project = snd

instance Monoid a => Injection b (a, b) where
  {-# INLINE embed #-}
  embed b = (mempty, b)

instance (Functor f, Bifunctor g, Monoid a) => Injection (f (g () b)) (f (g a b)) where
  {-# INLINE embed #-}
  embed = firstF (const mempty)
