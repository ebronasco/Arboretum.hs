module RootedTree (
    RootedTree(RootedTree, root, children),
    addChild,
    graft,
) where

import Symbolics
import GradedList

data RootedTree a = RootedTree {
    root :: a,
    children :: [RootedTree a]
} deriving (Show, Eq)

instance Graded (RootedTree a) where
    grading (RootedTree _ []) = 0
    grading (RootedTree _ xs) = 1 + sum (map grading xs)

type RootedTreeSpace k a = VectorSpace (k, RootedTree a)

addChild :: RootedTree a -> RootedTree a -> RootedTree a
addChild t (RootedTree x xs) = RootedTree x (t:xs)

graft :: (Eq a, Show a) => RootedTree a -> RootedTree a -> RootedTreeSpace Integer a
graft t1 t2 = vector $ (basisTerm $ addChild t1 t2) : (map (basisTerm . (addChild t1)) (children t2))
