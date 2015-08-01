{-# LANGUAGE ExistentialQuantification, ViewPatterns, TypeOperators, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Control.Folding where

import Prelude hiding
  ( any, all, and, or, sum, product
  , zip, length, head, last, elem
  , maximum, maybe, foldl, filter
  , minimum, take, drop, id, (.)
  )

import Data.Serialize
import Data.ByteString (ByteString)

import Data.Conduit (Sink, await)
import Data.Copointed
import qualified Data.Maybe as Maybe
import Data.Monoid
import Data.Functor.Identity
import Data.Functor.Apply
import Data.Functor.Extend
import Data.Functor.Contravariant
import Data.Bifunctor
import Data.Biapplicative
import Data.Key
import Data.Pointed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Semigroupoid
import Data.Foldable (Foldable, foldl)

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Comonad.Cofree

-- * Data Types

-- ** Step Function

-- | ':->:' is a bifunctor which is contravariant
-- in the first argument, and invariant in the second.
type a :->: b = b -> a -> b

-- | Maps the input of the step function contravariantly via @f@.
-- Synonymous for @'rmap' ('lmap' f)@.
inmap :: (b -> a) -> (a :->: c) -> (b :->: c)
inmap f = rmap (lmap f)

-- | Maps the output of the step function invariantly via @f@ and @g@.
-- Synonymous for @'dimap' g ('rmap' f)@.
outmap :: (b -> c) -> (c -> b) -> (a :->: b) -> (a :->: c)
outmap f g = dimap g (rmap f)

-- ** Initial Element

data Init a b = Zero b | One (a -> b)
  deriving Functor

instance Profunctor Init where
  lmap _ (Zero b) = Zero b
  lmap f (One g)  = One (g . f)
  rmap = fmap

peel :: Init a b -> (a :->: b) -> (a -> b)
peel (Zero b) f = f b
peel (One f) _ = f

-- ** Fold Types

data Fold a b where
  Fold :: (Init a x) -> (a :->: x) -> (x -> b) -> Fold a b

fold :: (a :->: b) -> b -> Fold a b
fold f b = Fold (Zero b) f id

fold1 :: (a :->: b) -> (a -> b) -> Fold a b
fold1 f g = Fold (One g) f id

instance Functor (Fold a) where
  fmap f (Fold i g s) = Fold i g (f . s)

instance Profunctor Fold where
  lmap f (Fold i g s) = Fold (lmap f i) (inmap f g) s
  rmap = fmap

newtype Foldette a b c d = Foldette (Fold a b -> Fold c d)

newtype Folding a b = Folding (a -> Cofree ((->) a) b)

-- * Functor

instance Functor (Folding a) where
  fmap f (Folding g) = Folding $ fmap (fmap f) g

-- * Combine

combine :: Folding a b -> Folding a' b' -> Folding (a, a') (b, b')
combine (Folding f) (Folding g) = Folding $ combineF f g
  where combineF f' g' (a, a') = combineCofree (f' a) (g' a')
        combineCofree (b :< f') (b' :< g') = (b, b') :< combineF f' g'

combineInit :: (a :->: b) -> (a' :->: b') -> Init a b -> Init a' b' -> Init (a, a') (b, b')
combineInit _ _ (Zero b) (Zero b') = Zero (b, b')
combineInit f g i j = One $ \(a, a') -> (peel i f a, peel j g a')

combineFold :: Fold a b -> Fold a' b' -> Fold (a, a') (b, b')
combineFold (Fold i f s) (Fold j g t) = Fold (combineInit f g i j) h u
  where h = \(b, b') (a, a') -> (f b a, g b' a')
        u = \(x, x') -> (s x, t x')

-- * Profunctor

instance Profunctor Folding where
  lmap f (Folding g) = Folding $ lmapCofree . g . f
    where lmapCofree (b :< g') = b :< lmapCofree . g'. f
  rmap = fmap

-- * Zip

instance Zip (Folding a) where
  zip folding = lmap (\a -> (a, a)) . combine folding

instance Zip (Fold a) where
  zip ld = lmap (\a -> (a, a)) . combineFold ld

-- * Pointed

instance Pointed (Folding a) where
  point b = Folding pointCofree
    where pointCofree _ = b :< pointCofree

instance Pointed (Fold a) where
  point b = Fold (Zero ()) (\_ _ -> ()) (const b)

-- * Apply

instance Apply (Folding a) where
  (<.>) = zap

instance Apply (Fold a) where
  (<.>) = zap

-- * Applicative

instance Applicative (Folding a) where
  pure = point
  (<*>) = zap

instance Applicative (Fold a) where
  pure = point
  (<*>) = zap

-- * Compose

compose :: Folding a b -> Folding b c -> Folding a (b, c)
compose (Folding f) (Folding g) = Folding $ composeF f g
  where composeF f' g' a = let cofree = f' a
                           in composeCofree cofree (g' (extract cofree))
        composeCofree (b :< f') (c :< g') = (b, c) :< composeF f' g'

composeInit :: (b :->: y) -> (x -> b) -> Init a x -> Init b y -> Init a (x, y)
composeInit f s i j = rmap (\x -> (x, peel j f (s x))) i

composeFold :: Fold a b -> Fold b c -> Fold a (b, c)
composeFold (Fold i f s) (Fold j g t) = Fold (composeInit g s i j) h u
  where h = \(x, y) a -> let x' = f x a in (x', g y (s x'))
        u = \(x, y) -> (s x, t y)

-- * Semigroupoid

instance Semigroupoid Folding where
  o foldingBC foldingAB = snd <$> compose foldingAB foldingBC

instance Semigroupoid Fold where
  o foldBC foldAB = snd <$> composeFold foldAB foldBC

-- * Category

instance Category Folding where
  id = Folding idCofree
    where idCofree a = a :< idCofree
  (.) = o

instance Category Fold where
  id = Fold (One id) (const id) id
  (.) = o

-- * Arrow

instance Arrow Folding where
  first folding = combine folding id
  arr f = Folding arrCofree
    where arrCofree a = f a :< arrCofree

instance Arrow Fold where
  first = flip combineFold id
  arr f = Fold (One f) (const f) id

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
