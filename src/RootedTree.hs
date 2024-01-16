module RootedTree (
    RootedTree(RootedTree, root, children),
    addChild,
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

addChild :: RootedTree a -> RootedTree a -> RootedTree a
addChild t (RootedTree x xs) = RootedTree x (t:xs)

