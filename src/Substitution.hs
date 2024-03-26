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
    GraftOp (..),
    evaluate,
    toOperad,
    substituteOp,
    substituteOpBy,
    countLeaves,
    substitute,
) where

import Data.Group
import qualified Data.List as L
import GradedList
import RootedTree
import Symbolics

data GraftOp a = Node (GraftOp a) (GraftOp a) | Leaf a deriving (Eq)

instance (Graded a) => Graded (GraftOp a) where
    grading (Leaf a) = grading a
    grading (Node a b) = grading a + grading b

instance Show a => Show (GraftOp a) where
    show (Leaf a) = show a
    show (Node a b) = "(" ++ show a ++ " graft " ++ show b ++ ")"

{- | Evaluate the @GraftOp@ by replacing nodes with @graftFF@ and evaluating.

Example:

>>> evaluate $ Node (Leaf 1) (Leaf 2)
(1 *^ 2[1])_2
>>> evaluate $ Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
(1 *^ 3[2[1]] + 1 *^ 3[1,2])_3
-}
evaluate :: (Eq a, Graded a) => GraftOp a -> PowerSeries Integer (PRTree a)
evaluate (Leaf a) = vector $ 1 *^ PRTree a []
evaluate (Node a b) =
    linear ((1 *^) . head) $
        bilinear graftFF (linear (: []) $ evaluate a) (linear (: []) $ evaluate b)

{- | Represent a @PRTree@ using the @graftFF@ operation encoding the binary tree using @GraftOp@.

Example:

>>> toOperad $ PRTree 1 [PRTree 2 [], PRTree 3 []]
(1 *^ (2 graft (3 graft 1)) + -1 *^ ((2 graft 3) graft 1))_3
>>> toOperad $ PRTree 1 [PRTree 2 [PRTree 4 [], PRTree 5 []], PRTree 3 []]
(1 *^ ((4 graft (5 graft 2)) graft (3 graft 1)) + -1 *^ (((4 graft 5) graft 2) graft (3 graft 1)) + -1 *^ (((4 graft (5 graft 2)) graft 3) graft 1) + 1 *^ ((((4 graft 5) graft 2) graft 3) graft 1))_5
-}
toOperad :: (Eq a, Graded a) => PRTree a -> PowerSeries Integer (GraftOp a)
toOperad (PRTree a []) = vector $ (1 *^) $ Leaf a
toOperad (PRTree a (b : bs)) =
    bilinear (\x y -> 1 *^ Node x y) (toOperad b) (toOperad $ PRTree a bs)
        <> invert (linear (toOperad . PRTree a) ([b] `graftFF` bs))

{- | Count the number of leaves of @GraftOp@. Equivalently, count the number of inputs of the corresponding operad element.

Example:

>>> countLeaves $ Node (Leaf 1) (Leaf 2)
2
>>> countLeaves $ Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
3
-}
countLeaves :: GraftOp a -> Int
countLeaves (Leaf _) = 1
countLeaves (Node a b) = countLeaves a + countLeaves b

{- | Substitute the leaves of @obj@ by the `GraftOp` elements in @ops@ in all possible orders.

Example:

>>> substituteOp [Leaf 1, Leaf 2] $ Node (Leaf 3) (Leaf 4)
(1 *^ (1 graft 2) + 1 *^ (2 graft 1))_2
>>> substituteOp [Node (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Node (Leaf 5) (Node (Leaf 6) (Leaf 7))
(1 *^ ((1 graft 2) graft (3 graft 4)) + 1 *^ (3 graft ((1 graft 2) graft 4)) + 1 *^ (4 graft (3 graft (1 graft 2))) + 1 *^ (3 graft (4 graft (1 graft 2))) + 1 *^ (4 graft ((1 graft 2) graft 3)) + 1 *^ ((1 graft 2) graft (4 graft 3)))_4
-}
substituteOp :: (Eq b, Graded b) => [GraftOp b] -> GraftOp a -> PowerSeries Integer (GraftOp b)
substituteOp ops obj = vector $ fromListS $ map ((1 *^) . (`substituteOpBy` obj)) $ L.permutations ops

{- | Substitute the leaves of @obj@ by the `GraftOp` elements in @ops@ following the given order.

Example:

>>> substituteOpBy [Leaf 1, Leaf 2] $ Node (Leaf 3) (Leaf 4)
(1 graft 2)
>>> substituteOpBy [Node (Leaf 1) (Leaf 2), Leaf 3, Leaf 4] $ Node (Leaf 5) (Node (Leaf 6) (Leaf 7))
((1 graft 2) graft (3 graft 4))
-}
substituteOpBy :: [GraftOp b] -> GraftOp a -> GraftOp b
substituteOpBy [x] (Leaf _) = x
substituteOpBy _ (Leaf _) = error "substituteOpBy: too many arguments"
substituteOpBy ops obj@(Node a b)
    | countLeaves obj == length ops =
        Node (substituteOpBy (take (countLeaves a) ops) a) (substituteOpBy (drop (countLeaves a) ops) b)
    | otherwise = error "substituteOpBy: wrong number of arguments"

{- | Substitute the vertices of @obj@ by the @PRTree@ elements in @gens@.

Example:

>>> substitute [PRTree 1 [], PRTree 2 []] $ PRTree 3 [PRTree 4 []]
(1 *^ 2[1] + 1 *^ 1[2])_2
>>> substitute [PRTree 1 [PRTree 2 []], PRTree 3 []] $ PRTree 4 [PRTree 5 []]
(1 *^ 3[1[2]] + 1 *^ 1[2[3]] + 1 *^ 1[3,2])_3
-}
substitute :: (Eq a, Graded a, Eq b, Graded b) => [PRTree b] -> PRTree a -> PowerSeries Integer (PRTree b)
substitute gens obj = linear evaluate $ bilinear substituteOp gensLinComb $ toOperad obj
  where
    gensLinComb = morphism (linear (: []) . toOperad) $ vector gens
