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
    ForestOp (..),
    evaluate,
    toOperad,
    permComposeOp,
    composeOp,
    countLeaves,
    substitute,
) where

import Data.Group
import qualified Data.List as L
import Data.Maybe
import GradedList
import Output
import RootedTree
import Symbolics

-- * Aromas

data Marked a = Marked a | Mark deriving (Eq)

instance (Show a) => Show (Marked a) where
    show (Marked a) = show a
    show Mark = "x"

instance (Graded a) => Graded (Marked a) where
    grading (Marked a) = grading a
    grading Mark = 0

instance (Texifiable a) => Texifiable (Marked a) where
    texify (Marked a) = texify a
    texify Mark = "x"

data AromaOp a = AromaOp [ForestOp (Marked a)] deriving (Eq)

instance (Show a) => Show (AromaOp a) where
    show (AromaOp as) = show as

instance (Graded a) => Graded (AromaOp a) where
    grading (AromaOp as) = sum $ map grading as

instance (Texifiable a) => Texifiable (AromaOp a) where
    texify (AromaOp as) = texify $ as


-- * Forests

data ForestOp a
    = Concat [ForestOp a]
    | Graft (ForestOp a) (ForestOp a)
    | Leaf a deriving (Eq)

instance (Graded a) => Graded (ForestOp a) where
    grading (Leaf a) = grading a
    grading (Graft a b) = grading a + grading b
    grading (Concat as) = sum $ map grading as

instance (Show a) => Show (ForestOp a) where
    show (Leaf a) = show a
    show (Graft a b) = "(" ++ show a ++ " graft " ++ show b ++ ")"
    show (Concat as) = show as

toPRTree :: ForestOp a -> PRTree (Maybe a)
toPRTree (Leaf a) = PRTree (Just a) []
toPRTree (Graft a b) = PRTree Nothing [toPRTree a, toPRTree b]
toPRTree (Concat as) = PRTree Nothing $ map toPRTree as

instance (Texifiable a) => Texifiable (Maybe a) where
    texify (Just a) = texify a
    texify Nothing = "_"

instance (Texifiable a) => Texifiable (ForestOp a) where
    texify = texify . toPRTree

{- | Evaluate the @GraftOp@ by replacing nodes with @graftFF@ and evaluating.

Example:

>>> evaluate $ Graft (Leaf 1) (Leaf 2)
(1 *^ 2[1])_2
>>> evaluate $ Graft (Leaf 1) (Graft (Leaf 2) (Leaf 3))
(1 *^ 3[2[1]] + 1 *^ 3[1,2])_3
-}
evaluate :: (Eq a, Graded a) => ForestOp a -> PowerSeries Integer [PRTree a]
evaluate (Leaf a) = vector $ 1 *^ [PRTree a []]
evaluate (Graft a b) = bilinear graftFF (evaluate a) (evaluate b)
evaluate (Concat as) = product $ map evaluate as

{- | Represent a @PRTree@ using the @graftFF@ operation encoding the binary tree using @GraftOp@.

Example:

>>> toOperad $ PRTree 1 [PRTree 2 [], PRTree 3 []]
(1 *^ (2 graft (3 graft 1)) + -1 *^ ((2 graft 3) graft 1))_3
>>> toOperad $ PRTree 1 [PRTree 2 [PRTree 4 [], PRTree 5 []], PRTree 3 []]
(1 *^ ((4 graft (5 graft 2)) graft (3 graft 1)) + -1 *^ (((4 graft 5) graft 2) graft (3 graft 1)) + -1 *^ (((4 graft (5 graft 2)) graft 3) graft 1) + 1 *^ ((((4 graft 5) graft 2) graft 3) graft 1))_5
-}
toOperad :: (Eq a, Graded a) => [PRTree a] -> ForestOp a
toOperad [] = Concat []
toOperad [PRTree a []] = Leaf a
toOperad [PRTree a bs] = Graft (toOperad bs) (Leaf a)
toOperad ts = Concat  $ map (toOperad . (:[])) ts

{- | Count leaves of @GraphOp a@ decorated by @x@.

Example:

>>> countLeaves 1 $ Graft (Leaf 1) (Leaf 2)
1
>>> countLeaves 1 $ Graft (Leaf 1) (Graft (Leaf 1) (Leaf 2))
2
-}
countLeaves :: (Eq a) => a -> ForestOp a -> Int
countLeaves x (Leaf y) = if x == y then 1 else 0
countLeaves x (Graft a b) = countLeaves x a + countLeaves x b
countLeaves x (Concat as) = sum $ map (countLeaves x) as

{- | Substitute the leaves decorated by @X@ of @obj@ by the `GraftOp` elements in @ops@ in all possible orders.

Example:

>>> substituteOp 3 [Leaf 1, Leaf 2] $ Graft (Leaf 3) (Leaf 3)
(1 *^ (1 graft 2) + 1 *^ (2 graft 1))_2
>>> substituteOp 5 [Graft (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Graft (Leaf 5) (Graft (Leaf 5) (Leaf 5))
(1 *^ ((1 graft 2) graft (3 graft 4)) + 1 *^ (3 graft ((1 graft 2) graft 4)) + 1 *^ (4 graft (3 graft (1 graft 2))) + 1 *^ (3 graft (4 graft (1 graft 2))) + 1 *^ (4 graft ((1 graft 2) graft 3)) + 1 *^ ((1 graft 2) graft (4 graft 3)))_4
-}
permComposeOp :: (Eq a, Graded a) => a -> [ForestOp a] -> ForestOp a -> PowerSeries Integer (ForestOp a)
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
composeOp :: (Eq a) => a -> [ForestOp a] -> ForestOp a -> Maybe (ForestOp a)
composeOp _ [] (Leaf y) = Just $ Leaf y
composeOp _ [y] (Leaf _) = Just y
composeOp _ _ (Leaf _) = Nothing
composeOp _ _ (Concat []) = Just $ Concat []
composeOp x ops obj
    | countLeaves x obj == length ops =
        Just $ case obj of
            Graft a b -> Graft
                (fromJust $ composeOp x (take (countLeaves x a) ops) a)
                (fromJust $ composeOp x (drop (countLeaves x a) ops) b)
            Concat as -> Concat $ map (\(a, ops_a) -> fromJust $ composeOp x ops_a a) $ spreadOps ops as
    | otherwise = Nothing
  where
    spreadOps os [a] = [(a, os)]
    spreadOps os (a:as) = (a, take (countLeaves x a) os) : (spreadOps (drop (countLeaves x a) os) as)

{- | Substitute the vertices decorated by @x@ of @obj@ by the @PRTree@ elements in @gens@.

Example:

>>> substitute 3 [PRTree 1 [], PRTree 2 []] $ PRTree 3 [PRTree 3 []]
(1 *^ 2[1] + 1 *^ 1[2])_2
>>> substitute 4 [PRTree 1 [PRTree 2 []], PRTree 3 []] $ PRTree 4 [PRTree 4 []]
(1 *^ 3[1[2]] + 1 *^ 1[2[3]] + 1 *^ 1[3,2])_3
-}
substitute :: (Eq a, Graded a) => a -> [PRTree a] -> [PRTree a] -> PowerSeries Integer [PRTree a]
substitute x gens obj = linear evaluate $ permComposeOp x (map (toOperad . (:[])) gens) (toOperad obj)
