module Substitution (
    GraftOp(..),
    evaluate,
    toOperad,
    substituteOp,
    substituteOpBy,
    countLeaves,
) where

import Data.Group
import qualified Data.List as L

import RootedTree
import Symbolics
import GradedList

data GraftOp a = Node (GraftOp a) (GraftOp a) | Leaf a deriving (Show, Eq)

instance Graded a => Graded (GraftOp a) where
    grading (Leaf a) = grading a
    grading (Node a b) = grading a + grading b

evaluate :: (Eq a, Graded a) => GraftOp a -> PowerSeries Integer (PRTree a)
evaluate (Leaf a) = vector $ 1 *^ (PRTree a [])
evaluate (Node a b) =
    linear ((1*^) . head) $
        bilinear graftFF (linear (:[]) $ evaluate a) (linear (:[]) $ evaluate b)

toOperad :: (Eq a, Graded a) => PRTree a -> PowerSeries Integer (GraftOp a)
toOperad (PRTree a []) = vector $ (1*^) $ Leaf a
toOperad (PRTree a (b:bs))
    = (bilinear (\x y -> 1 *^ (Node x y)) (toOperad b) (toOperad $ PRTree a bs))
        <> invert (linear toOperad (linear ((1*^) . (PRTree a)) $ [b] `graftFF` bs))

countLeaves :: GraftOp a -> Int
countLeaves (Leaf _) = 1
countLeaves (Node a b) = countLeaves a + countLeaves b

substituteOp :: (Eq b, Graded b) => [GraftOp b] -> GraftOp a -> PowerSeries Integer (GraftOp b)
substituteOp ops obj = vector $ fromListS $ map ((1*^) . (`substituteOpBy` obj)) $ L.permutations ops

substituteOpBy :: [GraftOp b] -> GraftOp a -> GraftOp b
substituteOpBy [x] (Leaf _) = x
substituteOpBy ops (Leaf _) = error "substituteOpBy: too many arguments"
substituteOpBy ops obj@(Node a b)
    | countLeaves obj == length ops
        = Node (substituteOpBy (take (countLeaves a) ops) a) (substituteOpBy (drop (countLeaves a) ops) b)
    | otherwise = error "substituteOpBy: wrong number of arguments"
