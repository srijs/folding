{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Control.Folding
( -- * Data Types
  -- ** Step
    Step, inmap, outmap
  -- ** Fold
  , Fold(..), fold, foldM, fold1
  -- ** These
  , These, fromThese, fromEither, fromTuple
  -- * Composition
  , combine, these, choose
  -- * Running
  , run, scan
  -- * Folds
  , concat, head, last
  , and, or, sum, product
  , all, any, null, length
  , maximum, minimum, elem, notElem
) where

import Prelude hiding
  ( any, all, and, or, sum, product
  , zip, length, head, last, elem
  , notElem, concat, null, zipWith
  , maximum, maybe, foldl, filter
  , minimum, take, drop, id, (.)
  )

import Data.Copointed
import qualified Data.Maybe as Maybe
import Data.Monoid
import Data.Functor.Identity
import Data.Functor.Apply
import Data.Functor.Extend
import Data.Functor.Contravariant
import Data.Bifunctor (bimap)
import Data.Bifunctor.Biff
import Data.Biapplicative (Biapplicative, bipure, biliftA2)
import Data.Bitraversable
import Data.Key
import Data.Pointed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Semigroupoid
import Data.Foldable (Foldable, foldl, toList)

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad (MonadPlus, mzero)

-- * Data Types

-- ** Step

-- | A bifunctor which is contravariant
-- in the first argument, and invariant in the second.
type Step a b = b -> a -> b

-- | Maps the input of the step function contravariantly via @f@.
-- Synonymous for @'rmap' ('lmap' f)@.
inmap :: (b -> a) -> Step a c -> Step b c
inmap f = rmap (lmap f)

-- | Maps the output of the step function invariantly via @f@ and @g@.
-- Synonymous for @'dimap' g ('rmap' f)@.
outmap :: (b -> c) -> (c -> b) -> Step a b -> Step a c
outmap f g = dimap g (rmap f)

-- ** These

-- | Represents the datatype /(unit + a + b + ab)/,
-- which is isomorphic to @('Maybe' a, 'Maybe' b)@.
type These a b = Biff (,) Maybe Maybe a b

fromThese :: a -> b -> These a b -> (a, b)
fromThese a b = bimap (Maybe.fromMaybe a) (Maybe.fromMaybe b) . runBiff

fromEither :: (Biapplicative p, Alternative f, Alternative g) => Either a b -> Biff p f g a b
fromEither (Left a) = Biff $ bipure (pure a) empty
fromEither (Right b) = Biff $ bipure empty (pure b)

fromTuple :: (Biapplicative p, Applicative f, Applicative g) => (a, b) -> Biff p f g a b
fromTuple = uncurry bipure

-- ** Fold

data Fold f a b where
  Fold :: x -> Step a x -> (x -> f b) -> Fold f a b

-- | Constructs a fold from a step function and an initial element.
fold :: Applicative f => Step a b -> f b -> Fold f a b
fold f b = Fold b (\fb a -> liftA (`f` a) fb) id

-- | Constructs a fold from a monadic step function and a monadic initial element.
foldM :: Monad m => (b -> a -> m b) -> m b -> Fold m a b
foldM f b = Fold b (\m a -> m >>= flip f a) id

-- | Constructs a fold from a step function.
--   The fold will produce @'empty'@ until it is fed with
--   the first @a@.
fold1 :: Alternative f => Step a a -> Fold f a a
fold1 f = Fold Nothing f' (Maybe.fromMaybe empty)
  where f' Nothing a = Just $ pure a
        f' (Just b) a = Just $ liftA (`f` a) b

instance Functor f => Functor (Fold f a) where
  fmap f (Fold i g s) = Fold i g (fmap (fmap f) s)

instance Functor f => Profunctor (Fold f) where
  lmap f (Fold i g s) = Fold i (inmap f g) s
  rmap = fmap

instance Functor f => Sieve (Fold f) f where
  sieve (Fold i f s) a = s (f i a)

instance (Foldable f, Alternative f) => Strong (Fold f) where
  first' = first

instance Applicative f => Zip (Fold f a) where
  zip ld = lmap (\a -> bipure a a) . combine ld

instance Applicative f => Pointed (Fold f a) where
  point b = Fold () (\_ _ -> ()) (const $ pure b)

instance Applicative f => Apply (Fold f a) where
  (<.>) = zap

instance Applicative f => Applicative (Fold f a) where
  pure = point
  (<*>) = zap

instance Foldable f => Semigroupoid (Fold f) where
  (Fold j g t) `o` (Fold i f s) = Fold k h u
    where k = (i, foldl g j (s i))
          h (x, y) a = let x' = f x a in (x', foldl g y (s x'))
          u = snd . bimap s t

instance (Alternative f, Foldable f) => Category (Fold f) where
  id = fold1 (const id)
  (.) = o

instance (Alternative f, Foldable f) => Arrow (Fold f) where
  first = flip combine id
  arr f = lmap f id

-- * Composition

-- | Combines two folds using any biapplicative and bitraversable bifunctor.
-- A generalization of @'***'@. Works with @(,)@, @'Const'@, @'These'@, etc.
combine :: (Applicative f, Biapplicative p, Bitraversable p) => Fold f a b -> Fold f a' b' -> Fold f (p a a') (p b b')
combine (Fold i f s) (Fold j g t) = Fold (bipure i j) (biliftA2 f g) (bitraverse s t)

these :: Zip f => Fold f a b -> Fold f a' b' -> Fold f (These a a') (b, b')
these (Fold i f s) (Fold j g t) = Fold (i, j) h u
  where h (x, y) = fromThese x y . bimap (f x) (g y)
        u = uncurry zip . bimap s t

choose :: Zip f => Fold f a b -> Fold f a' b' -> Fold f (Either a a') (b, b')
choose fa fb = lmap fromEither (these fa fb)

-- * Running

run :: Foldable g => Fold f a b -> g a -> f b
run (Fold i f s) as = s $ foldl f i as

scan :: Foldable g => Fold f a b -> g a -> [f b]
scan (Fold i f s) as = map s $ scanl f i $ toList as

-- * Folds

concat :: (Applicative f, Monoid a) => Fold f a a
concat = fold mappend (pure mempty)

head :: (Alternative f) => Fold f a a
head = fold1 const

last :: Alternative f => Fold f a a
last = fold1 (const id)

and :: Applicative f => Fold f Bool Bool
and = fold (&&) (pure True)

or :: Applicative f => Fold f Bool Bool
or = fold (||) (pure False)

sum :: (Applicative f, Num a) => Fold f a a
sum = fold (+) (pure 0)

product :: (Applicative f, Num a) => Fold f a a
product = fold (*) (pure 1)

all :: (Applicative f) => (a -> Bool) -> Fold f a Bool
all = flip lmap and

any :: (Applicative f) => (a -> Bool) -> Fold f a Bool
any = flip lmap or

null :: Applicative f => Fold f a Bool
null = all (const False)

length :: Applicative f => Fold f a Int
length = lmap (const 1) sum

maximum :: (Alternative f, Ord a) => Fold f a a
maximum = fold1 max

minimum :: (Alternative f, Ord a) => Fold f a a
minimum = fold1 min

elem :: (Applicative f, Eq a) => a -> Fold f a Bool
elem a = any (a==)

notElem :: (Applicative f, Eq a) => a -> Fold f a Bool
notElem a = all (a/=)
