{-# LANGUAGE ExistentialQuantification #-}

module Control.Folding where

import Prelude hiding (any, all, and, or, sum)

import Data.Monoid
import Data.Profunctor
import Data.Serialize
import Data.ByteString (ByteString)

import Control.Comonad

data Fold a b = forall x. Fold
  (x -> a -> x) -- step function
  x -- initial
  (x -> b) -- extract
  (Putter x) -- encode
  (Get x) -- decode

instance Comonad (Fold a) where
  extract (Fold _ init extract _ _) = extract init
  extend f = wrap . f

instance Profunctor Fold where
  lmap f (Fold step init extract put get) = Fold (\x -> step x . f) init extract put get
  rmap f (Fold step init extract put get) = Fold step init (f . extract) put get

instance Functor (Fold a) where fmap = rmap

-- * State Serialization

putState :: Putter (Fold a b)
putState (Fold _ init _ put _) = put init

getState :: Fold a b -> Get (Fold a b)
getState (Fold step _ extract put get) = fmap (\init -> Fold step init extract put get) get

serializeState :: Fold a b -> ByteString
serializeState = runPut . putState

unserializeState :: Fold a b -> ByteString -> Either String (Fold a b)
unserializeState = runGet . getState

-- * Running

runList :: Fold a b -> [a] -> Fold a b
runList (Fold step init extract put get) as = Fold step (foldl step init as) extract put get

-- * Transformations

wrap :: forall a b. b -> Fold a b
wrap b = Fold (const (const ())) () (const b) put get

fold :: Serialize b => (b -> a -> b) -> b -> Fold a b
fold step init = Fold step init id put get

pair :: Fold a b -> Fold c d -> Fold (a, c) (b, d)
pair (Fold stepL initL extractL putL getL) (Fold stepR initR extractR putR getR)
  = Fold step init extract put get
  where
    step (xL, xR) (aL, aR) = (stepL xL aL, stepR xR aR)
    init = (initL, initR)
    extract (xL, xR) = (extractL xL, extractR xR)
    put = putTwoOf putL putR
    get = getTwoOf getL getR

head :: Serialize a => Fold a (Maybe a)
head = fold step Nothing
  where step (Just a) = const (Just a)
        step Nothing = Just

last :: Serialize a => Fold a (Maybe a)
last = fold (const Just) Nothing

and :: Fold Bool Bool
and = fold (&&) True

or :: Fold Bool Bool
or = fold (||) False

sum :: (Num a, Serialize a) => Fold a a
sum = fold (+) 0

product :: (Num a, Serialize a) => Fold a a
product = fold (*) 1

all :: (a -> Bool) -> Fold a Bool
all = flip lmap and

any :: (a -> Bool) -> Fold a Bool
any = flip lmap or

null :: Fold a Bool
null = all (const False)

length :: Fold a Int
length = lmap (const 1) sum

maximum :: (Ord a, Serialize a) => Fold a (Maybe a)
maximum = fold step Nothing
  where step Nothing = Just
        step (Just a) = Just . max a

minimum :: (Ord a, Serialize a) => Fold a (Maybe a)
minimum = fold step Nothing
  where step Nothing = Just
        step (Just a) = Just . min a

elem :: Eq a => a -> Fold a Bool
elem a = any (a==)

notElem :: Eq a => a -> Fold a Bool
notElem a = all (a/=)
