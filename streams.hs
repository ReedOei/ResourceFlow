{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Identity

import Data.Functor.Compose
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord

import Debug.Trace

-- groupWith :: Eq k => (k -> [a] -> [b] -> (k, c)) -> [(k,a)] -> [(k,b)] -> ([(k,a)], [(k,b)], [(k,c)])
-- groupWith f [] ys = ([], ys, [])
-- groupWith f xs [] = (xs, [], [])
-- groupWith f ((k,a):xs) ys =
--     let (takenXs, leftXs) = partition ((== k) . fst) xs
--         (takenYs, leftYs) = partition ((== k) . fst) ys
--         (leftFst, leftSnd, transformed) = groupWith f leftXs leftYs
--     in (leftFst, leftSnd, f k (a : map snd takenXs) (map snd takenYs) : transformed)

findKeyAndRemove :: Eq k => k -> [(k,a)] -> Maybe ((k,a), [(k,a)])
findKeyAndRemove k [] = Nothing
findKeyAndRemove k ((k',a):rest)
    | k == k' = Just ((k', a), rest)
    | otherwise =
        case findKeyAndRemove k rest of
            Nothing -> Nothing
            Just (res, left) -> Just (res, (k',a) : left)

groupWith :: Eq k => (k -> [a] -> [b] -> (k, c)) -> [(k,a)] -> [(k,b)] -> [(k,c)]
groupWith f [] [] = []
groupWith f [] ((k,b):ys) =
    let (takenYs, rest) = partition ((== k) . fst) ys
    in f k [] (b : map snd takenYs) : groupWith f [] rest
groupWith f ((k,a):xs) ys =
    let (takenXs, leftXs) = partition ((== k) . fst) xs
        (takenYs, leftYs) = partition ((== k) . fst) ys
    in f k (a : map snd takenXs) (map snd takenYs) : groupWith f leftXs leftYs

splitWith :: (Monoid b, Monoid c) => (a -> (b,c)) -> [a] -> (b, c)
splitWith f xs = mconcat $ map f xs

ifEmpty :: [a] -> b -> ([a] -> b) -> b
ifEmpty [] ys f = ys
ifEmpty xs ys f = f xs

fromNat :: Int -> [()]
fromNat n = replicate n ()

---------------------------------------------------------
--- These exists so that we can reduce how many auxiliary functions we need in the language
---------------------------------------------------------
pairMap :: ((a,b) -> c) -> [(a,b)] -> [c]
pairMap f = fst . splitWith (\x -> ([f x], []))

concatPairMap :: Monoid c => ((a,b) -> c) -> [(a,b)] -> c
concatPairMap f = mconcat . pairMap f

headOr :: a -> [a] -> a
headOr x xs = ifEmpty xs x head
---------------------------------------------------------
--- End
---------------------------------------------------------

data Val = Nat Integer | Boolean Bool | Multiset [Val] | Empty | Pair (Val, Val)
    deriving (Show, Eq)

instance Semigroup Val where
    Nat n <> Nat m = Nat $ n + m
    Boolean b1 <> Boolean b2 = Boolean $ b1 || b2
    Multiset m1 <> Multiset m2 = Multiset $ m1 ++ m2
    Pair p1 <> Pair p2 = Pair $ p1 <> p2

    Empty <> b = b
    a <> Empty = a

instance Monoid Val where
    mempty = Empty

class Monoid a => Value a where
    toVal :: a -> Val
    fromVal :: Val -> a

instance Value Val where
    toVal = id
    fromVal = id

instance Value () where
    toVal () = Nat 1
    fromVal _ = ()

instance Value Any where
    toVal (Any b) = Boolean b
    fromVal (Boolean b) = Any b

instance (Value a, Value b) => Value (a,b) where
    toVal (a, b) = Pair (toVal a, toVal b)
    fromVal (Pair (a, b)) = (fromVal a, fromVal b)

instance Value [()] where
    toVal xs = Nat $ genericLength xs
    fromVal (Multiset xs) = replicate (length xs) ()

instance (Value a, Value b) => Value [(a,b)] where
    toVal xs = Multiset $ map toVal xs
    fromVal (Multiset m) = map fromVal m

instance Value [a] => Value [[a]] where
    toVal xs = Multiset $ map toVal xs
    fromVal (Multiset m) = map fromVal m

class (Show k, Eq k) => Fresh k where
    fresh :: [k] -> k

    freshes :: [k] -> [k]
    freshes xs = let new = fresh xs in new : freshes (new : xs)

instance Fresh Integer where
    fresh [] = 0
    fresh xs = maximum xs + 1

instance Fresh (Sum Integer) where
    fresh [] = 0
    fresh xs = maximum xs + 1

instance Enum (Sum Integer) where
    toEnum = Sum . toEnum
    fromEnum = fromEnum . getSum

instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh xs = (fresh (map fst xs), fresh (map snd xs))

-- TODO: Replace Monoid by Resource
-- TODO: If we can make this abstraction a bit nicer, maybe more progress can be made...
data Locator a b where
    Locator :: (Monoid a, Monoid b)
                => (forall ka r. (Fresh ka, Monoid r) => [(ka,a)] -> (forall kb. Fresh kb => [(kb,b)] -> ([(kb,b)], r)) -> ([(ka,a)],r))
                -> Locator a b

runLocator :: [a] -> Locator a b -> ([a], [b])
runLocator vals (Locator f) =
    let (taggedRet, sel) = f (zip ([0..] :: [Integer]) vals) $ \taggedVals -> ([], map snd taggedVals)
    in (map snd taggedRet, sel)

runDestination :: [a] -> Locator a b -> ([a], [b])
runDestination vals (Locator f) =
    let (taggedRet, sel) = f (zip ([0..] :: [Integer]) vals) $ \taggedVals -> (taggedVals, [])
    in (map snd taggedRet, sel)

(|>) :: Locator a b -> Locator b c -> Locator a c
(Locator f) |> (Locator g) = Locator $ \vals k ->
    f vals $ \taggedVals -> g taggedVals $ \finalVals -> k finalVals

-- flow :: a -> Locator a c -> Locator a c -> a
flow state src@Locator{} dst@Locator{} =
    let (newState, selected) = runLocator [state] src
        ([finalState], []) = runDestination newState (dst |> combine selected)
    in finalState

-- test :: [Locator a b] -> Locator [a] [b]

selectVals :: (Show a, Monoid a, Eq a) => [a] -> Locator [a] [a]
selectVals toTake = Locator $ \lists f ->
    let run [] lists = Just [(lists, mempty)]
        run leftToTake [] = Nothing
        run leftToTake ((k,vals):rest) =
            let taken = vals \\ (vals \\ leftToTake)
                tailRes = run (leftToTake \\ taken) rest in
            if taken == [] then
                (:) <$> pure ([(k,vals)], mempty) <*> tailRes
            else
                let (ret, sel) = f [(k, taken)]
                    grouped = groupWith (\k xs ys -> (k, concat $ xs ++ ys)) [(k, vals \\ taken)] ret
                in (:) <$> pure (grouped, sel) <*> tailRes
    in case run toTake lists of
        Nothing -> ([], mempty)
        Just results ->
            let (rets, sels) = splitWith (\(a,b) -> ([a],[b])) results
            in (concat rets, mconcat sels)

selectFst :: (Show a, Show b, Monoid a, Monoid b, Eq a) => Locator (a,b) a
selectFst = Locator $ \vals f ->
    let (fsts, snds) = splitWith (\(k,(a,b)) -> ([(k,a)], [(k,b)])) vals
        (ret, sel) = f fsts
        grouped = groupWith (\k xs ys -> (k, (mconcat xs, mconcat ys))) ret snds
    in (grouped, sel)

selectSnd :: (Monoid a, Monoid b, Eq a) => Locator (a,b) b
selectSnd = Locator $ \vals f ->
    let (fsts, snds) = splitWith (\(k,(a,b)) -> ([(k,a)], [(k,b)])) vals
        (ret, sel) = f snds
        grouped = groupWith (\k xs ys -> (k, (mconcat xs, mconcat ys))) fsts ret
    in (grouped, sel)

eachK :: Monoid b => (forall kb. Fresh kb => [(kb,[b])] -> ([(kb,[b])], r)) -> (forall kb. Fresh kb => [(kb,b)] -> ([(kb,b)], r))
eachK g transformed =
    let (ret, sel) = g $ pairMap (\(k,b) -> (k, [b])) transformed
    in (pairMap (\(k,bs) -> (k, headOr mempty bs)) ret, sel)

-- TODO: This should probably work with any functions f :: a -> c and g :: c -> a s.t. g . f = id (then this is just f = \x -> [x] and g = head)
each :: (Show a, Show b) => Locator a b -> Locator [a] [b]
each (Locator f) = Locator $ \lists g ->
    let temp = concatPairMap (\(k,vals) -> zipWith (\i v -> ((i,k), v)) ([0..] :: [Integer]) vals) lists
        temp2 = concatPairMap (\(k,vals) -> zipWith (\i v -> (k,(i,()))) ([0..] :: [Integer]) vals) lists
        (ret, sel) = f temp $ \transformed -> eachK g transformed
        finalGrouped = groupWith (\k xs ys -> (k, groupWith (\i xs' ys' -> (i, mconcat ys')) xs ys)) temp2 $ pairMap (\((i,k),v) -> (k,(i,v))) ret
    in (pairMap (\(k, vs) -> (k, pairMap snd vs)) finalGrouped, sel)

constructList :: (Show a, Eq a, Monoid a) => Locator a [a]
constructList = preConstructList |> each selectSnd

preConstructList :: (Show a, Eq a, Monoid a) => Locator a [(Sum Integer, a)]
preConstructList = Locator $ \vals f ->
    let indexed = zipWith (\i (_,a) -> (i,a)) [0..] vals
        (ret, sel) = f [(0 :: Sum Integer, indexed)]
        keyIndexed = zipWith (\i (k,a) -> (i,k)) [0..] vals
        grouped = groupWith (\idx xs ys -> (idx, (head ys, mconcat xs))) (concatPairMap snd ret) keyIndexed
    in (pairMap snd grouped, sel)

combine :: Monoid a => [a] -> Locator a a
combine vals = Locator $ \rest k ->
    let (ret, sel) = k rest
        -- (xs, ys, grouped) = groupWith (\k a b -> (k, mconcat $ a <> b)) ret vals
    in (zipWith (\(k,a) b -> (k, a <> b)) ret vals, sel)

selectList :: Eq a => [a] -> [a] -> ([a], [a])
selectList xs ys = (xs \\ ys, ys \\ xs)

selectUnit :: () -> () -> ((), ())
selectUnit a b = ((), ())

summation :: (Eq a, Monoid a) => (a -> a -> (a, a)) -> Locator [a] a
summation select = Locator $ \vals f ->
    let (ret, sel) = f $ pairMap (\(k,v) -> (k, mconcat v)) vals
        redistribute _ [] = []
        redistribute [] _ = []
        redistribute ((k,vals):rest) (x:xs) =
            let (leftoverX, leftoverVals, filled) = fill vals x
            in if leftoverX == mempty then
                (k,filled) : redistribute ((k,leftoverVals):rest) xs
               else
                (k,filled) : redistribute rest (leftoverX:xs)

        fill [] x = (x, [], [])
        fill (y:ys) x =
            let (newY, selected) = select y x
                (newX, taken) = select x y in
            if newY == mempty then
                if newX == mempty then (mempty, ys, [y])
                else
                    let (leftoverX, leftoverVals, filled) = fill ys newX
                    in (leftoverX, leftoverVals, y : filled)
            else
                if newX == mempty then (mempty, newY:ys, [selected])
                else
                    let (leftoverX, leftoverVals, filled) = fill ys newX
                    in (leftoverX, newY : leftoverVals, selected : filled)
    in (redistribute vals $ pairMap snd ret, sel)
