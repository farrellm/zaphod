{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Class where

import qualified Data.Text as T

class Render a where
  render :: a -> Text

class MaybeList a where
  isList :: a -> Bool
  maybeList :: a -> Maybe [a]

class HasLocation f where
  location :: f a -> a

class Location l where
  getBegin :: l -> l
  getEnd :: l -> l

setLocation :: (Functor f) => b -> f () -> f b
setLocation b = (const b <$>)

stripLocation :: (Functor f) => f a -> f ()
stripLocation = (const () <$>)

instance Render () where
  render () = "()"
  {-# INLINE render #-}

instance (Render a) => Render [a] where
  render xs = "(" <> T.intercalate " " (render <$> xs) <> ")"
  {-# INLINE render #-}

instance (Render a) => Render (NonEmpty a) where
  render xs = "(" <> T.intercalate " " (render <$> toList xs) <> ")"
  {-# INLINE render #-}

instance (Render a, Render b) => Render (a, b) where
  render (l, r) = "(" <> render l <> " . " <> render r <> ")"
  {-# INLINE render #-}

instance (Render a, Render b, Render c) => Render (a, b, c) where
  render (a, b, c) = "(" <> render a <> " . " <> render b <> " . " <> render c <> ")"
  {-# INLINE render #-}

instance Location () where
  getBegin () = ()
  getEnd () = ()

instance (Functor f, Location l) => Location (f l) where
  getBegin x = getBegin <$> x
  getEnd x = getEnd <$> x
