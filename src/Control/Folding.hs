{-# LANGUAGE GADTs #-}

module Control.Folding
( -- * Data Types
  -- ** Step
    Step, inmap, outmap
  -- ** Fold
  , Fold(..), fold, fold1
  -- ** These
  , These, fromThese, fromEither, fromTuple
  -- * Composition
  , combine, these, choose
) where

import Prelude hiding
  ( any, all, and, or, sum, product
  , zip, length, head, last, elem
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
import Data.Foldable (Foldable, foldl)
import qualified Data.List as List

import Control.Applicative
import Control.Arrow
import Control.Category

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

fold :: Applicative f => Step a b -> b -> Fold f a b
fold f b = Fold b f pure

fold1 :: Alternative f => Step a b -> (a -> b) -> Fold f a b
fold1 f g = Fold Nothing f' (Maybe.maybe empty pure)
  where f' Nothing a = Just $ g a
        f' (Just b) a = Just $ f b a

instance Functor f => Functor (Fold f a) where
  fmap f (Fold i g s) = Fold i g (fmap (fmap f) s)

instance Functor f => Profunctor (Fold f) where
  lmap f (Fold i g s) = Fold i (inmap f g) s
  rmap = fmap

instance (Foldable f, Alternative f) => Strong (Fold f) where
  first' = first

instance Applicative f => Zip (Fold f a) where
  zip ld = lmap (\a -> (a, a)) . combine ld

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
  id = fold1 (const id) id
  (.) = o

instance (Alternative f, Foldable f) => Arrow (Fold f) where
  first = flip combine id
  arr f = fold1 (const f) f

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

{-
type instance Key (Fold a) = Integer

instance Keyed (Fold a) where
  mapWithKey f (Fold step init finalize) = Fold
    (\(k, x) a -> (succ k, step x a))
    (0, init)
    (\(k, x) -> f k (finalize x))

instance ZipWithKey (Fold a)

instance Adjustable (Fold a) where
  adjust f k fold = mapWithKey f' fold
    where f' k' a | k == k' = f a
                  | otherwise = a

-- * State Serialization

-- state :: Lens (Fold a b) (Either String (Fold a b)) ByteString ByteString
state :: Functor f
      => (ByteString -> f ByteString) -> Fold a b -> f (Either String (Fold a b))
state f fold = fmap (runGet $ getState fold) (f . runPut $ putState fold)
  where
    putState (Fold _ init _ ) = put init
    getState (Fold step _ finalize) = fmap (\init -> Fold step init finalize) get

serializeState :: Fold a b -> ByteString
serializeState = getConst . state Const

unserializeState :: Fold a b -> ByteString -> Either String (Fold a b)
unserializeState fd b = runIdentity $ state (const $ Identity b) fd

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

compose :: Fold a b -> Fold b c -> Fold a (b, c)
compose (Fold (flip -> stepL) initL finalizeL)
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
filter p = lmap f . maybe
  where f a = if p a then Just a else Nothing

take :: Integer -> Fold a b -> Fold a b
take l (Fold step init finalize)
  = Fold step' (0, init) (finalize.snd)
    where
      step' (i, x) a | i < l = (i + 1, step x a)
                     | otherwise = (i, x)

drop :: Integer -> Fold a b -> Fold a b
drop l (Fold step init finalize)
  = Fold step' (0, init) (finalize.snd)
    where
      step' (i, x) a | i < l = (i + 1, x)
                     | otherwise = (i, step x a)

-- * Folds

concat :: (Monoid a, Serialize a) => Fold a a
concat = fold mappend mempty

head :: Serialize a => Fold1 a a
head = fold1 const

last :: Serialize a => Fold1 a a
last = fold1 (const id)

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
notElem a = all (a/=)-}
