module Control.Folding.Internal.SnocList where

import Prelude hiding (foldl)

import Data.Foldable
import Data.Monoid
import Data.Serialize

data SnocList a = Snoc (SnocList a) a | Lin
  deriving Show

fromList :: [a] -> SnocList a
fromList = foldl Snoc Lin 

instance Foldable SnocList where
  foldMap f (Snoc as a) = foldMap f as <> f a
  foldMap _ Lin = mempty

instance Serialize a => Serialize (SnocList a) where
  put = put . toList
  get = fmap fromList get
