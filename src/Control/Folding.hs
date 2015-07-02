{-# LANGUAGE ExistentialQuantification, MonadComprehensions, ViewPatterns, TypeOperators #-}

module Control.Folding where

import Prelude hiding
  ( any, all, and, or, sum
  , zip, length, head, last
  , maximum, maybe, foldl
  )

import Data.Serialize
import Data.ByteString (ByteString)

import Data.Conduit (Sink, await)
import Data.Copointed
import qualified Data.Maybe as Maybe
import Data.Monoid
import Data.Functor.Contravariant
import Data.Bifunctor
import Data.Biapplicative
import Data.Key
import Data.Pointed
import Data.Profunctor
import Data.Foldable (Foldable, foldl)

import Control.Applicative
import Control.Monad hiding (foldM)
import Control.Monad.Zip
import Control.Comonad

import Control.Folding.Internal.SnocList

data Fold a b = forall x. Serialize x => Fold
  (x -> a -> x) -- step
  x -- init
  (x -> b) -- finalize

type Fold1 a b = Fold a (Maybe b)

newtype Cofold b a = Cofold { getFold :: Fold a b }

instance Profunctor Fold where
  lmap f (Fold step init finalize)
    = Fold (\x -> step x . f) init finalize
  rmap f (Fold step init finalize)
    = Fold step init (f . finalize)

instance Functor (Fold a) where fmap = rmap

instance Contravariant (Cofold a) where
  contramap f = Cofold . lmap f . getFold

instance Zip (Fold a) where
  zip a = lmap (\a -> (a, a)) . combine a

instance Pointed (Fold a) where
  point b = Fold (const (const ())) () (const b)

instance Copointed (Fold a) where
  copoint (Fold _ init finalize) = finalize init

instance Applicative (Fold a) where
  pure = point
  (<*>) = zap

instance Serialize a => Monad (Fold a) where
  return = point
  (>>=) fold = join . flip rmap fold
    where
      join (Fold stepL initL finalizeL)
        = Fold step' init' finalize'
        where
          step' (x, as) a = (stepL x a, Snoc as a)
          init' = (initL, Lin)
          finalize' (x, as) = run (finalizeL x) as

instance Serialize a => MonadZip (Fold a) where
  mzip = zip

instance Comonad (Fold a) where
  extract = copoint
  extend f = point . f

-- * State Serialization

putState :: Putter (Fold a b)
putState (Fold _ init _ ) = put init

getState :: Fold a b -> Get (Fold a b)
getState (Fold step _ finalize)
  = fmap (\init -> Fold step init finalize) get

serializeState :: Fold a b -> ByteString
serializeState = runPut . putState

unserializeState :: Fold a b -> ByteString -> Either String (Fold a b)
unserializeState = runGet . getState

-- * Running

fun :: Fold :-> (->)
fun (Fold step init finalize) = finalize . step init

run :: Foldable f => Fold a b -> f a -> b
run fold = extract . process fold

sink :: Monad m => Fold a b -> Sink a m b
sink fold = await >>= Maybe.maybe (return (extract fold))
                                  (sink . processOne fold)

processOne :: Fold a b -> a -> Fold a b
processOne (Fold step init finalize) a
  = Fold step (step init a) finalize

process :: Foldable f => Fold a b -> f a -> Fold a b
process (Fold step init finalize) as
  = Fold step (foldl step init as) finalize

scannify :: Fold a b -> Fold a [b]
scannify (Fold step init finalize)
  = Fold step' init' finalize'
  where
    step' (x:xs) a = step x a : x : xs
    init' = [init]
    finalize' = reverse . map finalize

-- * Construction

fold :: Serialize b => (b -> a -> b) -> b -> Fold a b
fold step init = Fold step init id

fold1 :: Serialize a => (a -> a -> a) -> Fold1 a a
fold1 step = fold (flip step') Nothing
  where step' a = Just . Maybe.maybe a (flip step a)

foldWithIndex :: Serialize b => (Int -> b -> a -> b) -> b -> Fold a b
foldWithIndex f b = Fold step (0, b) snd
  where step (idx, b) a = (idx + 1, f idx b a)

foldM :: (Monad m, Serialize (m b)) =>
         (b -> a -> m b) -> m b -> Fold a (m b)
foldM step init = Fold step' init id
  where step' mb a = mb >>= flip step a

foldM_ :: (Monad m, Serialize (m b)) =>
          (b -> a -> m b) -> m b -> Fold a (m ())
foldM_ step init = rmap (>> return ()) (foldM step init)

-- * Composition

compose :: Fold a b -> Fold b c -> Fold a c
compose foldL = rmap snd . compose' foldL

compose' :: Fold a b -> Fold b c -> Fold a (b, c)
compose' (Fold (flip -> stepL) initL finalizeL)
         (Fold (flip -> stepR) initR finalizeR)
  = Fold (flip step) init finalize
  where
    step a = apply . first (stepL a)
    init = apply $ bipure initL initR
    finalize = bimap finalizeL finalizeR
    apply x = (second . stepR . finalizeL $ fst x) x

combine :: Fold a b -> Fold a' b' -> Fold (a, a') (b, b')
combine (Fold stepL initL finalizeL)
        (Fold stepR initR finalizeR)
  = Fold step init finalize
  where
    step = (<<*>>) . bimap stepL stepR
    init = bipure initL initR
    finalize = bimap finalizeL finalizeR

choose :: Fold a b -> Fold a' b' -> Fold (Either a a') (b, b')
choose (Fold (flip -> stepL) initL finalizeL)
       (Fold (flip -> stepR) initR finalizeR)
  = Fold (flip step) init finalize
  where
    step = either (first . stepL) (second . stepR)
    init = bipure initL initR
    finalize = bimap finalizeL finalizeR

-- * Transformations

maybe :: Fold a b -> Fold (Maybe a) b
maybe (Fold step init finalize)
  = Fold step' init finalize
  where
    step' x = Maybe.maybe x (step x)

filter :: (a -> Bool) -> Fold a b -> Fold a b
filter p fold = lmap f (maybe fold)
  where f a = if p a then Just a else Nothing

-- * Folds

concat :: (Monoid a, Serialize a) => Fold a a
concat = fold mappend mempty

head :: Serialize a => Fold1 a a
head = fold1 const

last :: Serialize a => Fold1 a a
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

maximum :: (Ord a, Serialize a) => Fold1 a a
maximum = fold1 max

minimum :: (Ord a, Serialize a) => Fold1 a a
minimum = fold1 min

elem :: Eq a => a -> Fold a Bool
elem a = any (a==)

notElem :: Eq a => a -> Fold a Bool
notElem a = all (a/=)
