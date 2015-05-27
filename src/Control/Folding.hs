{-# LANGUAGE ExistentialQuantification #-}

module Control.Folding where

import Prelude hiding (any, all, and, or, sum, zip, length)

import Data.Serialize
import Data.ByteString (ByteString)

import Data.Monoid
import Data.Functor.Contravariant
import Data.Profunctor

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Comonad

data Fold a b = forall x. Fold
  (x -> a -> x) -- step
  x -- init
  (x -> b) -- finalize
  (Putter x) -- encode
  (Get x) -- decode

newtype Cofold b a = Cofold { getFold :: Fold a b }

instance Profunctor Fold where
  lmap f (Fold step init finalize put get)
    = Fold (\x -> step x . f) init finalize put get
  rmap f (Fold step init finalize put get)
    = Fold step init (f . finalize) put get

instance Functor (Fold a) where fmap = rmap

instance Contravariant (Cofold a) where
  contramap f = Cofold . lmap f . getFold

instance Applicative (Fold a) where
  pure = return
  (<*>) = ap

instance Monad (Fold a) where
  return b = Fold (const (const ())) () (const b) put get
  (>>=) fold f = f (extract fold)

instance Comonad (Fold a) where
  extract (Fold _ init finalize _ _) = finalize init
  extend f = return . f

-- * State Serialization

putState :: Putter (Fold a b)
putState (Fold _ init _ put _) = put init

getState :: Fold a b -> Get (Fold a b)
getState (Fold step _ finalize put get) = fmap (\init -> Fold step init finalize put get) get

serializeState :: Fold a b -> ByteString
serializeState = runPut . putState

unserializeState :: Fold a b -> ByteString -> Either String (Fold a b)
unserializeState = runGet . getState

-- * Running

runList :: Fold a b -> [a] -> Fold a b
runList (Fold step init finalize put get) as
  = Fold step (foldl step init as) finalize put get

-- * Construction

fold :: Serialize b => (b -> a -> b) -> b -> Fold a b
fold step init = Fold step init id put get

foldWithIndex :: Serialize b => (Int -> b -> a -> b) -> b -> Fold a b
foldWithIndex f b = Fold step (0, b) snd (putTwoOf put put) (getTwoOf get get)
  where step (idx, b) a = (idx + 1, f idx b a)

-- * Composition

compose :: Fold a b -> Fold b c -> Fold a c
compose foldL = rmap snd . composeR foldL

composeL :: Fold a b -> Fold (a, b) c -> Fold a c
composeL foldL = rmap snd . composeLR foldL

composeR :: Fold a b -> Fold b c -> Fold a (b, c)
composeR foldL = composeLR foldL . lmap snd

composeLR :: Fold a b -> Fold (a, b) c -> Fold a (b, c)
composeLR (Fold stepL initL finalizeL putL getL)
          (Fold stepR initR finalizeR putR getR)
  = Fold step init finalize put get
  where
    step (xL, xR) a = let xL' = stepL xL a in (xL', stepR xR (a, finalizeL xL'))
    init = (initL, initR)
    finalize (xL, xR) = (finalizeL xL, finalizeR xR)
    put = putTwoOf putL putR
    get = getTwoOf getL getR

-- * Arrow-like

-- Arrow (***)
zip :: Fold a b -> Fold a' b' -> Fold (a, a') (b, b')
zip (Fold stepL initL finalizeL putL getL)
    (Fold stepR initR finalizeR putR getR)
  = Fold step init finalize put get
  where
    step (xL, xR) (aL, aR) = (stepL xL aL, stepR xR aR)
    init = (initL, initR)
    finalize (xL, xR) = (finalizeL xL, finalizeR xR)
    put = putTwoOf putL putR
    get = getTwoOf getL getR

-- Arrow (&&&)
split :: Fold a b -> Fold a b' -> Fold a (b, b')
split (Fold stepL initL finalizeL putL getL)
      (Fold stepR initR finalizeR putR getR)
  = Fold step init finalize put get
  where
    init = (initL, initR)
    step (xL, xR) a = (stepL xL a, stepR xR a)
    finalize (xL, xR) = (finalizeL xL, finalizeR xR)
    put = putTwoOf putL putR
    get = getTwoOf getL getR

-- * Transformation

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
