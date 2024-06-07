{-# LANGUAGE TupleSections #-}

{- |
Module      : Substitution
Description : Implementation of substitution of planar rooted trees
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

We use the operadic approach to substitution of planar rooted trees.
-}
module Substitution (
    Marked (..),
    SyntacticTree (..),
    eval,
    syn,
    symCompose,
    compose,
    countLeaves,
    substitute,
) where

import AromaticTree
import Data.Group
import qualified Data.List as L
import Data.Maybe
import Data.Typeable
import Debug.Trace
import GradedList
import Output
import RootedTree
import Symbolics

-- * Mark

data Marked a = Marked a | Mark deriving (Eq)

instance (Show a) => Show (Marked a) where
    show (Marked a) = "m" ++ show a
    show Mark = "x"

instance (Graded a) => Graded (Marked a) where
    grading (Marked a) = grading a
    grading Mark = 0

instance (Texifiable a) => Texifiable (Marked a) where
    texify (Marked a) = texify a
    texify Mark = "x"

class Markable a where
    mark :: a b -> a (Marked b)
    unmark :: a (Marked b) -> a b

instance Markable PRTree where
    mark (PRTree a bs) = PRTree (Marked a) (map mark bs)
    unmark (PRTree (Marked a) bs) = PRTree a $ map unmark bs

instance Markable PAroma where
    mark (PAroma (Cycle ts)) = PAroma $ Cycle $ map mark ts
    unmark (PAroma (Cycle ts)) = PAroma $ Cycle $ map unmark ts

markAPF (as, ts) = (map mark as, map mark ts)

unmarkAPF (as, ts) = (map unmark as, map unmark ts)

-- * Forests

data SyntacticTree a
    = Concat [SyntacticTree a]
    | Graft (SyntacticTree a) (SyntacticTree a)
    | Leaf (Marked a)
    | Trace (SyntacticTree a)
    deriving (Eq)

instance (Graded a) => Graded (SyntacticTree a) where
    grading (Leaf a) = grading a
    grading (Graft a b) = grading a + grading b
    grading (Concat as) = sum $ map grading as
    grading (Trace a) = grading a

instance (Show a) => Show (SyntacticTree a) where
    show (Leaf a) = show a
    show (Graft a b) = "(" ++ show a ++ " graft " ++ show b ++ ")"
    show (Concat as) = show as
    show (Trace a) = "Tr " ++ show a


instance (Show a, Texifiable a) => Texifiable (SyntacticTree a) where
    texify = texify . toTree
      where 
        toTree (Leaf a) = PRTree (show a) []
        toTree (Graft a b) = PRTree "$\\curvearrowright$" [toTree a, toTree b]
        toTree (Concat as) = PRTree "$\\cdot$" $ map toTree as
        toTree (Trace a) = PRTree "Tr" [toTree a]

{- | Evaluate the @GraftOp@ by replacing nodes with @graftFF@ and evaluating.

Example:

>>> eval $ Graft (Leaf 1) (Leaf 2)
(1 *^ 2[1])_2
>>> eval $ Graft (Leaf 1) (Graft (Leaf 2) (Leaf 3))
(1 *^ 3[2[1]] + 1 *^ 3[1,2])_3
-}
eval :: (Show a, Texifiable a, Typeable a, Eq a, Graded a) => SyntacticTree a -> PowerSeries Integer (APForest a)
eval = linear unmarkAPF . evaluate'
  where
    evaluate' (Leaf a) = vector $ 1 *^ ([], [PRTree a []])
    evaluate' (Graft a b) = bilinear graftAF (evaluate' a) (evaluate' b)
    evaluate' (Concat as) = product $ map evaluate' as
    evaluate' (Trace a) = linear connectRootToMarked $ evaluate' a
      where
        connectRootToMarked (as, t : ts) = case (searchMarkTree (as, t)) of
            Nothing -> searchMarkAroma (as, t)
            Just x -> vector $ 1 *^ x
        searchMarkTree (as, t) = case (filter ((== PRTree Mark []) . last) $ branchPaths t) of
            [] -> Nothing
            l -> Just $ (,[]) $ (: as) $ PAroma $ Cycle $ init $ head l
        searchMarkAroma (as, t) = substitute Mark [([], t)] (as, [])

{- | Represent a @PRTree@ using the @graftFF@ operation encoding the binary tree using @GraftOp@.

Example:

>>> syn $ PRTree 1 [PRTree 2 [], PRTree 3 []]
(1 *^ (2 graft (3 graft 1)) + -1 *^ ((2 graft 3) graft 1))_3
>>> syn $ PRTree 1 [PRTree 2 [PRTree 4 [], PRTree 5 []], PRTree 3 []]
(1 *^ ((4 graft (5 graft 2)) graft (3 graft 1)) + -1 *^ (((4 graft 5) graft 2) graft (3 graft 1)) + -1 *^ (((4 graft (5 graft 2)) graft 3) graft 1) + 1 *^ ((((4 graft 5) graft 2) graft 3) graft 1))_5
-}
syn :: (Eq a, Graded a) => APForest a -> SyntacticTree a
syn = toOperad' . markAPF
  where
    toOperad' ([], []) = Concat []
    toOperad' ([PAroma (Cycle ts)], []) = Trace $ toOperad' $ ([],) $ (: []) $ breakCycle ts
      where
        breakCycle [] = PRTree Mark []
        breakCycle (t : ts) = addBranch (breakCycle ts) t
        addBranch b (PRTree a bs) = PRTree a (b : bs)
    toOperad' ([], [PRTree a []]) = Leaf a
    toOperad' ([], [PRTree a bs]) = Graft (toOperad' ([], bs)) (Leaf a)
    toOperad' (as, ts) =
        Concat $
            (map (toOperad' . (,[]) . (: [])) as)
                ++ (map (toOperad' . ([],) . (: [])) ts)

{- | Count leaves of @GraphOp a@ decorated by @x@.

Example:

>>> countLeaves 1 $ Graft (Leaf 1) (Leaf 2)
1
>>> countLeaves 1 $ Graft (Leaf 1) (Graft (Leaf 1) (Leaf 2))
2
-}
countLeaves :: (Eq a) => a -> SyntacticTree a -> Int
countLeaves x (Leaf Mark) = 0
countLeaves x (Leaf (Marked y)) = if x == y then 1 else 0
countLeaves x (Graft a b) = countLeaves x a + countLeaves x b
countLeaves x (Concat as) = sum $ map (countLeaves x) as
countLeaves x (Trace a) = countLeaves x a

{- | Substitute the leaves decorated by @X@ of @obj@ by the `GraftOp` elements in @ops@ in all possible orders.

Example:

>>> symCompose 3 [Leaf 1, Leaf 2] $ Graft (Leaf 3) (Leaf 3)
(1 *^ (1 graft 2) + 1 *^ (2 graft 1))_2
>>> symCompose 5 [Graft (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Graft (Leaf 5) (Graft (Leaf 5) (Leaf 5))
(1 *^ ((1 graft 2) graft (3 graft 4)) + 1 *^ (3 graft ((1 graft 2) graft 4)) + 1 *^ (4 graft (3 graft (1 graft 2))) + 1 *^ (3 graft (4 graft (1 graft 2))) + 1 *^ (4 graft ((1 graft 2) graft 3)) + 1 *^ ((1 graft 2) graft (4 graft 3)))_4
-}
symCompose :: (Eq a, Graded a) => a -> [SyntacticTree a] -> SyntacticTree a -> PowerSeries Integer (SyntacticTree a)
symCompose x ops obj =
    mconcat
        $ map
            ( \perm_ops -> case compose x perm_ops obj of
                Just g -> vector (1 *^ g)
                Nothing -> vector Zero
            )
        $ L.permutations ops

{- | Substitute the leaves decorated by @x@ of @obj@ by the `GraftOp` elements in @ops@ following the given order.

Example:

>>> compose 3 [Leaf 1, Leaf 2] $ Graft (Leaf 3) (Leaf 3)
(1 graft 2)
>>> compose 5 [Graft (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Graft (Leaf 5) (Graft (Leaf 5) (Leaf 5))
((1 graft 2) graft (3 graft 4))
-}
compose :: (Eq a) => a -> [SyntacticTree a] -> SyntacticTree a -> Maybe (SyntacticTree a)
compose _ [] (Leaf y) = Just $ Leaf y
compose _ [y] (Leaf _) = Just y
compose _ _ (Leaf _) = Nothing
compose _ _ (Concat []) = Just $ Concat []
compose x ops obj
    | countLeaves x obj == length ops =
        Just $ case obj of
            Graft a b ->
                Graft
                    (fromJust $ compose x (take (countLeaves x a) ops) a)
                    (fromJust $ compose x (drop (countLeaves x a) ops) b)
            Concat as -> Concat $ map (\(a, ops_a) -> fromJust $ compose x ops_a a) $ spreadOps ops as
            Trace a -> Trace $ fromJust $ compose x ops a
    | otherwise = Nothing
  where
    spreadOps os [a] = [(a, os)]
    spreadOps os (a : as) = (a, take (countLeaves x a) os) : (spreadOps (drop (countLeaves x a) os) as)

{- | Substitute the vertices decorated by @x@ of @obj@ by the @PRTree@ elements in @gens@.

Example:

>>> substitute 3 [PRTree 1 [], PRTree 2 []] $ PRTree 3 [PRTree 3 []]
(1 *^ 2[1] + 1 *^ 1[2])_2
>>> substitute 4 [PRTree 1 [PRTree 2 []], PRTree 3 []] $ PRTree 4 [PRTree 4 []]
(1 *^ 3[1[2]] + 1 *^ 1[2[3]] + 1 *^ 1[3,2])_3
-}
substitute :: (Eq a, Graded a, Show a, Texifiable a, Typeable a) => a -> [APTree a] -> APForest a -> PowerSeries Integer (APForest a)
substitute x gens obj = linear eval $ symCompose x (map (syn . (\(as, t) -> (as, [t]))) gens) (syn obj)
