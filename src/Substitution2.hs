{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Substitution
Description : Implementation of substitution of planar rooted trees
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

We use the operadic approach to substitution of planar rooted trees.
-}
module Substitution2 (
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
import AromaticTree
import Symbolics

-- * Mark

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

-- * Operad

class Operad a where
    type Decoration a
    type AlgebraBasis a
    type AlgebraScalars a

    evaluate :: a -> PowerSeries (AlgebraScalars a) (AlgebraBasis a)

    toOperad :: AlgebraBasis a -> PowerSeries (AlgebraScalars a) a

    compose :: (Decoration a) -> [a] -> a -> a

-- * Trees

data TreeOp a
    = Graft (ForestOp a) (TreeOp a)
    | TLeaf a deriving (Eq)

instance (Graded a) => Graded (TreeOp a) where
    grading (TLeaf a) = grading a
    grading (Graft a b) = grading a + grading b

instance (Show a) => Show (TreeOp a) where
    show (TLeaf a) = show a
    show (Graft a b) = "(" ++ show a ++ " graft " ++ show b ++ ")"

instance (Eq a) => Operad (TreeOp a) where
    type Decoration (TreeOp a) = a
    type AlgebraBasis (TreeOp a) = PRTree a
    type AlgebraScalars (TreeOp a) = Integer

    evaluate (TLeaf a) = vector $ 1 *^ PRTree a []
    evaluate (Graft a b) = bilinear graftFT (evaluate a) (evaluate b)

    toOperad (PRTree a bs) = Graft (toOperad bs) (TLeaf a)

    compose x [y] (TLeaf z) = if x == z then y else TLeaf z
    compose x ts (Graft a b) =
        Graft
            (compose (take n_leaves_b ts) a)
            (compose (drop n_leaves_b ts) b)
      where
        n_leaves_b = countLeaves x b
        countLeaves (TLeaf y) = if x == y then 1 else 0
        countLeaves (Graft a b) = countLeaves a + countLeaves b


instance Texifiable (TreeOp a) where
    texify = texify . toTree
      where
        toTree (TLeaf a) = PRTree (show a) []
        toTree (Graft a b) = PRTree "i_$\\curvearrowright$" [toTree a, toTree b]

-- * Forests

data ForestOp a = Concat [TreeOp a] deriving (Eq)

instance (Graded a) => Graded (ForestOp a) where
    grading (Concat as) = sum $ map grading as

instance (Show a) => Show (ForestOp a) where
    show (Concat as) = show as

instance (Show a) => Operad (ForestOp a) where
    type AlgebraBasis (ForestOp a) = [PRTree a]
    type AlgebraScalars (ForestOp a) = Integer

    evaluate (Concat as) = product $ map evaluate as

    toOperad ts = linear Concat $ product $ map ((linear (:[])) . toOperad) ts



instance Texifiable (TreeOp a) where
    texify = texify . toTree
      where
        toTree (Concat as) = PRTree "i_$\\curvearrowright$" $ map toTree as


{-
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
evaluate (Trace a) = connectRootToMarked $ evaluate a
  where
      connectRootToMarked t = Aroma $ head $ filter ((== Mark) . last) $ branchPaths t

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
-}
