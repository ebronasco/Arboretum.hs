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
    AForestOp (..),
    evaluate,
    toOperad,
    permComposeOp,
    composeOp,
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

-- !!! TODO: Make all leaves of AForestOp marked. Then, when you evaluate, you get marked forest which you can unmark at the very end. Since all vertices are homogeneously marked, you don't need to nest the marks and mark/unmark all the time.

-- * Aromas

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

data AForestOp a
    = Trace (AForestOp a)
    | Concat [AForestOp a]
    | Graft (AForestOp a) (AForestOp a)
    | Leaf (Marked a)
    deriving (Eq)

instance (Graded a) => Graded (AForestOp a) where
    grading (Leaf a) = grading a
    grading (Graft a b) = grading a + grading b
    grading (Concat as) = sum $ map grading as
    grading (Trace a) = grading a

instance (Show a) => Show (AForestOp a) where
    show (Leaf a) = show a
    show (Graft a b) = "(" ++ show a ++ " graft " ++ show b ++ ")"
    show (Concat as) = show as
    show (Trace a) = "Tr " ++ show a

toPRTree :: (Show a) => AForestOp a -> PRTree String
toPRTree (Leaf a) = PRTree (show a) []
toPRTree (Graft a b) = PRTree "$\\curvearrowright$" [toPRTree a, toPRTree b]
toPRTree (Concat as) = PRTree "$\\cdot$" $ map toPRTree as
toPRTree (Trace a) = PRTree "Tr" [toPRTree a]

instance (Show a, Texifiable a) => Texifiable (AForestOp a) where
    texify = texify . toPRTree

{- | Evaluate the @GraftOp@ by replacing nodes with @graftFF@ and evaluating.

Example:

>>> evaluate $ Graft (Leaf 1) (Leaf 2)
(1 *^ 2[1])_2
>>> evaluate $ Graft (Leaf 1) (Graft (Leaf 2) (Leaf 3))
(1 *^ 3[2[1]] + 1 *^ 3[1,2])_3
-}
evaluate :: (Show a, Texifiable a, Typeable a, Eq a, Graded a) => AForestOp a -> PowerSeries Integer (APForest a)
{-
evaluate (Leaf a) = (\res -> trace ("leaf " ++ show a ++ " = " ++ show res) res) $ vector $ 1 *^ ([], [PRTree a []])
evaluate (Graft a b) = (\res -> trace ("graft " ++ show a ++ " onto " ++ show b ++ " = " ++ show res) res) $ bilinear graftAF (evaluate a) (evaluate b)
evaluate (Concat as) = (\res -> trace ("concat " ++ show as ++ " = " ++ show res) res) $ product $ map evaluate as
evaluate (Trace a) =(\res -> trace ("trace " ++ show a ++ " = " ++ show res) res) $ linear connectRootToMarked $ evaluate a
-}
evaluate = linear unmarkAPF . evaluate'
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

>>> toOperad $ PRTree 1 [PRTree 2 [], PRTree 3 []]
(1 *^ (2 graft (3 graft 1)) + -1 *^ ((2 graft 3) graft 1))_3
>>> toOperad $ PRTree 1 [PRTree 2 [PRTree 4 [], PRTree 5 []], PRTree 3 []]
(1 *^ ((4 graft (5 graft 2)) graft (3 graft 1)) + -1 *^ (((4 graft 5) graft 2) graft (3 graft 1)) + -1 *^ (((4 graft (5 graft 2)) graft 3) graft 1) + 1 *^ ((((4 graft 5) graft 2) graft 3) graft 1))_5
-}
toOperad :: (Eq a, Graded a) => APForest a -> AForestOp a
toOperad = toOperad' . markAPF
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
countLeaves :: (Eq a) => a -> AForestOp a -> Int
countLeaves x (Leaf Mark) = 0
countLeaves x (Leaf (Marked y)) = if x == y then 1 else 0
countLeaves x (Graft a b) = countLeaves x a + countLeaves x b
countLeaves x (Concat as) = sum $ map (countLeaves x) as
countLeaves x (Trace a) = countLeaves x a

{- | Substitute the leaves decorated by @X@ of @obj@ by the `GraftOp` elements in @ops@ in all possible orders.

Example:

>>> substituteOp 3 [Leaf 1, Leaf 2] $ Graft (Leaf 3) (Leaf 3)
(1 *^ (1 graft 2) + 1 *^ (2 graft 1))_2
>>> substituteOp 5 [Graft (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Graft (Leaf 5) (Graft (Leaf 5) (Leaf 5))
(1 *^ ((1 graft 2) graft (3 graft 4)) + 1 *^ (3 graft ((1 graft 2) graft 4)) + 1 *^ (4 graft (3 graft (1 graft 2))) + 1 *^ (3 graft (4 graft (1 graft 2))) + 1 *^ (4 graft ((1 graft 2) graft 3)) + 1 *^ ((1 graft 2) graft (4 graft 3)))_4
-}
permComposeOp :: (Eq a, Graded a) => a -> [AForestOp a] -> AForestOp a -> PowerSeries Integer (AForestOp a)
permComposeOp x ops obj =
    mconcat
        $ map
            ( \perm_ops -> case composeOp x perm_ops obj of
                Just g -> vector (1 *^ g)
                Nothing -> vector Zero
            )
        $ L.permutations ops

{- | Substitute the leaves decorated by @x@ of @obj@ by the `GraftOp` elements in @ops@ following the given order.

Example:

>>> substituteOpBy 3 [Leaf 1, Leaf 2] $ Graft (Leaf 3) (Leaf 3)
(1 graft 2)
>>> substituteOpBy 5 [Graft (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Graft (Leaf 5) (Graft (Leaf 5) (Leaf 5))
((1 graft 2) graft (3 graft 4))
-}
composeOp :: (Eq a) => a -> [AForestOp a] -> AForestOp a -> Maybe (AForestOp a)
composeOp _ [] (Leaf y) = Just $ Leaf y
composeOp _ [y] (Leaf _) = Just y
composeOp _ _ (Leaf _) = Nothing
composeOp _ _ (Concat []) = Just $ Concat []
composeOp x ops obj
    | countLeaves x obj == length ops =
        Just $ case obj of
            Graft a b ->
                Graft
                    (fromJust $ composeOp x (take (countLeaves x a) ops) a)
                    (fromJust $ composeOp x (drop (countLeaves x a) ops) b)
            Concat as -> Concat $ map (\(a, ops_a) -> fromJust $ composeOp x ops_a a) $ spreadOps ops as
            Trace a -> Trace $ fromJust $ composeOp x ops a
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
substitute x gens obj = linear evaluate $ permComposeOp x (map (toOperad . (\(as, t) -> (as, [t]))) gens) (toOperad obj)
