{-# LANGUAGE ExistentialQuantification, MonadComprehensions #-}

module Control.Folding where

import Prelude hiding
  ( any, all, and, or, sum
  , zip, length, head, last
  , maximum, maybe, foldl
  )

import Data.Serialize
import Data.ByteString (ByteString)

import Data.Maybe as Maybe
import Data.Monoid
import Data.Functor.Contravariant
import Data.Bifunctor
import Data.Biapplicative
import Data.Profunctor
import Data.Foldable (Foldable, foldl)

import Control.Applicative
import Control.Monad
import Control.Monad.Zip
import Control.Comonad

import Control.Folding.Internal.SnocList

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

instance Serialize a => Applicative (Fold a) where
  pure = point
  (<*>) = ap

instance Serialize a => Monad (Fold a) where
  return = point
  (>>=) fold = join . flip rmap fold
    where
      join (Fold stepL initL finalizeL putL getL)
        = Fold step' init' finalize' put' get'
        where
          step' (x, as) a = (stepL x a, Snoc as a)
          init' = (initL, Lin)
          finalize' (x, as) = run (finalizeL x) as
          put' = putTwoOf putL put
          get' = getTwoOf getL get

instance Serialize a => MonadZip (Fold a) where
  mzip foldL = lmap (\a -> (a, a)) . combine foldL

instance Comonad (Fold a) where
  extract (Fold _ init finalize _ _) = finalize init
  extend f = point . f

-- * State Serialization

putState :: Putter (Fold a b)
putState (Fold _ init _ put _) = put init

getState :: Fold a b -> Get (Fold a b)
getState (Fold step _ finalize put get)
  = fmap (\init -> Fold step init finalize put get) get

serializeState :: Fold a b -> ByteString
serializeState = runPut . putState

unserializeState :: Fold a b -> ByteString -> Either String (Fold a b)
unserializeState = runGet . getState

-- * Running

run :: Foldable f => Fold a b -> f a -> b
run fold = extract . process fold

process :: Foldable f => Fold a b -> f a -> Fold a b
process (Fold step init finalize put get) as
  = Fold step (foldl step init as) finalize put get

scannify :: Fold a b -> Fold a [b]
scannify (Fold step init finalize put get)
  = Fold step' init' finalize' put' get'
  where
    step' (x:xs) a = step x a : x : xs
    init' = [init]
    finalize' = reverse . map finalize
    put' = putListOf put
    get' = getListOf get

-- * Construction

point :: b -> Fold a b
point b = Fold (const (const ())) () (const b) put get

fold :: Serialize b => (b -> a -> b) -> b -> Fold a b
fold step init = Fold step init id put get

fold1 :: Serialize a => (a -> a -> a) -> Fold a (Maybe a)
fold1 step = fold (flip step') Nothing
  where step' a = Just . Maybe.maybe a (flip step a)

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
    finalize = bimap finalizeL finalizeR
    put = putTwoOf putL putR
    get = getTwoOf getL getR

combine :: Fold a b -> Fold a' b' -> Fold (a, a') (b, b')
combine (Fold stepL initL finalizeL putL getL)
    (Fold stepR initR finalizeR putR getR)
  = Fold step init finalize put get
  where
    step = (<<*>>) . bimap stepL stepR
    init = (initL, initR)
    finalize = bimap finalizeL finalizeR
    put = putTwoOf putL putR
    get = getTwoOf getL getR

choose :: Fold a b -> Fold a' b' -> Fold (Either a a') (b, b')
choose (Fold stepL initL finalizeL putL getL)
       (Fold stepR initR finalizeR putR getR)
  = Fold step init finalize put get
  where
    step (xL, xR) (Left a) = (stepL xL a, xR)
    step (xL, xR) (Right a') = (xL, stepR xR a')
    init = (initL, initR)
    finalize = bimap finalizeL finalizeR
    put = putTwoOf putL putR
    get = getTwoOf getL getR

maybe :: Fold a b -> Fold (Maybe a) b
maybe (Fold step init finalize putX getX)
  = Fold step' init finalize putX getX
  where
    step' x = Maybe.maybe x (step x)

-- * Transformation

head :: Serialize a => Fold a (Maybe a)
head = fold1 const

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
maximum = fold1 max

minimum :: (Ord a, Serialize a) => Fold a (Maybe a)
minimum = fold1 min

elem :: Eq a => a -> Fold a Bool
elem a = any (a==)

notElem :: Eq a => a -> Fold a Bool
notElem a = all (a/=)
