{-# LANGUAGE OverloadedStrings #-}

module Zaphod.Types.Class where

import qualified Data.Text as T

class Render a where
  render :: a -> Text

class MaybeList a where
  isList :: a -> Bool
  maybeList :: a -> Maybe [a]

class Magma a where
  (><) :: a -> a -> a
  tuple :: NonEmpty a -> a

infixr 6 ><

class Semigroup l => Location l where
  locBegin :: l -> l
  locEnd :: l -> l

class Location (Locat a) => HasLocation a where
  type Value a
  type Locat a
  location :: a -> Locat a
  value :: a -> Value a
  withLocation :: Value a -> Locat a -> a

  splitLocation :: (HasLocation a) => a -> (Value a, Locat a)
  splitLocation x = (value x, location x)
  {-# INLINE splitLocation #-}

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
