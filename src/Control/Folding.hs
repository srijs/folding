{-# LANGUAGE ExistentialQuantification, ViewPatterns, TypeOperators, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

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

-- * Data Types

data Cofree h a = Cofree
  { unCofree :: (a, h (Cofree h a))
  } deriving Functor

newtype Fold' a b = Fold' { unFold :: Cofree ((->) a) b }

data Fold a b = Fold b (Folding a b)

newtype Folding a b = Folding (a -> Fold a b)

newtype Folding' a b = Folding' (a -> Fold' a b)

-- * Functor

instance Functor (Fold' a) where
  fmap f = Fold' . fmap f . unFold

instance Functor (Fold a) where
  fmap f (Fold a folding) = Fold (f a) $ fmap f folding

instance Functor (Folding a) where
  fmap f (Folding g) = Folding $ fmap (fmap f) g

instance Functor (Folding' a) where
  fmap f (Folding' g) = Folding' $ fmap (fmap f) g

-- * Combine

combineFolds :: Fold a b -> Fold a' b' -> Fold (a, a') (b, b')
combineFolds (Fold a folding) (Fold a' folding') = Fold (a, a') $ combine folding folding'

combine :: Folding a b -> Folding a' b' -> Folding (a, a') (b, b')
combine (Folding f) (Folding g) = Folding $ \(a, a') -> combineFolds (f a) (g a')

combineFolds' :: Fold' a b -> Fold' a' b' -> Fold' (a, a') (b, b')
combineFolds' (Fold' cofree) (Fold' cofree') = Fold' $ combineCofree cofree cofree'
  where combineF f g (a, a') = combineCofree (f a) (g a')
        combineCofree (Cofree (b, f)) (Cofree (b', g)) = Cofree $ ((b, b'), combineF f g)

combine' :: Folding' a b -> Folding' a' b' -> Folding' (a, a') (b, b')
combine' (Folding' f) (Folding' g) = Folding' $ \(a, a') -> combineFolds' (f a) (g a')

-- * Profunctor

instance Profunctor Fold where
  lmap f (Fold b folding) = Fold b $ lmap f folding
  rmap = fmap

instance Profunctor Folding where
  lmap f (Folding g) = Folding $ dimap f (lmap f) g
  rmap = fmap

instance Profunctor Fold' where
  lmap f (Fold' cofree) = Fold' $ lmapCofree f cofree
    where lmapCofree f' (Cofree (b, g)) = Cofree (b, dimap f' (lmapCofree f') g)
  rmap = fmap

instance Profunctor Folding' where
  lmap f (Folding' g) = Folding' $ dimap f (lmap f) g
  rmap = fmap

-- * Zip

instance Zip (Fold a) where
  zip fold = lmap (\a -> (a, a)) . combineFolds fold

instance Zip (Folding a) where
  zip folding = lmap (\a -> (a, a)) . combine folding

instance Zip (Fold' a) where
  zip fold = lmap (\a -> (a, a)) . combineFolds' fold

instance Zip (Folding' a) where
  zip folding = lmap (\a -> (a, a)) . combine' folding

-- * Pointed

instance Pointed (Fold a) where
  point b = Fold b (point b)

instance Pointed (Folding a) where
  point b = Folding $ point (point b)

instance Pointed (Fold' a) where
  point b = Fold' $ pointCofree b
    where pointCofree b' = Cofree (b', point (pointCofree b'))

instance Pointed (Folding' a) where
  point b = Folding' $ point (point b)

-- * Comonad

instance Copointed (Fold a) where
  copoint (Fold b _) = b

instance Copointed (Cofree h) where
  copoint (Cofree (a, _)) = a

instance Copointed (Fold' a) where
  copoint (Fold' cofree) = copoint cofree

instance Extend (Fold a) where
  extended f = point . f

instance Comonad (Fold a) where
  extract = copoint
  extend = extended

-- * Apply

instance Apply (Fold a) where
  (<.>) = zap

instance Apply (Folding a) where
  (<.>) = zap

instance Apply (Fold' a) where
  (<.>) = zap

instance Apply (Folding' a) where
  (<.>) = zap


-- * Applicative

instance Applicative (Fold a) where
  pure = point
  (<*>) = zap

instance Applicative (Fold' a) where
  pure = point
  (<*>) = zap

instance Applicative (Folding a) where
  pure = point
  (<*>) = zap

instance Applicative (Folding' a) where
  pure = point
  (<*>) = zap

-- * Compose

composeFolds :: Fold a b -> Fold b c -> Fold a (b, c)
composeFolds (Fold b foldingAB) (Fold c foldingBC) = Fold (b, c) $ compose foldingAB foldingBC

composeFolds' :: Fold' a b -> Fold' b c -> Fold' a (b, c)
composeFolds' (Fold' cofree) (Fold' cofree') = Fold' $ composeCofree cofree cofree'
  where composeF f g a = let cofree''@(Cofree (b, _)) = f a in composeCofree cofree'' (g b)
        composeCofree (Cofree (b, f)) (Cofree (c, g)) = Cofree ((b, c), composeF f g)

compose :: Folding a b -> Folding b c -> Folding a (b, c)
compose (Folding f) (Folding g) = Folding $ \a -> let fold@(Fold b _) = f a in composeFolds fold (g b)

compose' :: Folding' a b -> Folding' b c -> Folding' a (b, c)
compose' (Folding' f) (Folding' g) = Folding' $ \a -> let fold@(Fold' (Cofree (b, _))) = f a in composeFolds' fold (g b)

-- * Semigroupoid

instance Semigroupoid Fold where
  o foldBC foldAB = fmap snd $ composeFolds foldAB foldBC

instance Semigroupoid Fold' where
  o foldBC foldAB = fmap snd $ composeFolds' foldAB foldBC

instance Semigroupoid Folding where
  o foldingBC foldingAB = fmap snd $ compose foldingAB foldingBC

instance Semigroupoid Folding' where
  o foldingBC foldingAB = fmap snd $ compose' foldingAB foldingBC

-- * Category

instance Category Folding where
  id = Folding $ \a -> Fold a id
  (.) = o

instance Category Folding' where
  id = Folding' (Fold' . idCofree)
    where idCofree a = Cofree (a, idCofree)
  (.) = o

-- * Arrow

instance Arrow Folding where
  first folding = combine folding id
  arr f = Folding $ \a -> Fold (f a) (arr f)

instance Arrow Folding' where
  first folding = combine' folding id
  arr f = Folding' (Fold' . arrCofree)
    where arrCofree a = Cofree (f a, arrCofree)

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
