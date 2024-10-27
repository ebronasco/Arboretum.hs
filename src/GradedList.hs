{- |
Module      : GradedList
Description : Utilities for lists of graded elements.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of a @Graded@ typeclass and utilities for lists of
graded elements used in @Symbolics@ module.
-}
module GradedList (
    Graded,
    grading,
    NonDecreasingList,
    unNDecList,
    nDecList,
    distributeLists,
    distributeGradedLists,
    groupByGrading,
) where

import qualified Data.MultiSet as MS

{- | The @Graded@ typeclass is used to define the grading of an
element.
-}
class Graded t where
    grading :: t -> Integer

{- |
  @Integer@ is used to generate basis elements for testing
  @Symbolics.hs@.

Example:

>>> grading 123
1
>>> grading (-123)
1
-}
instance Graded Integer where
    grading _ = 1

{- |
  @Char@ can be useful to denote variables like @'x', 'y', 'z'@ when
  using @Symbolics.hs@. The grading of a character is 1.

Example:

>>> grading 'x'
1
-}
instance Graded Char where
    grading _ = 1

{- |
  The list structure is used to represent the non-commutative
  associative product in @Symbolics.hs@. The grading of a list is
  the sum of the gradings of its elements.

Example:

>>> grading [1, 2, 3]
3
>>> grading [[1, 2], [3, 4]]
4
-}
instance (Graded a) => Graded [a] where
    grading [] = 0
    grading (h : t) = grading h + grading t

{- |
  The MultiSet structure is used to represent the commutative
  associative product in @Symbolics.hs@. The grading of a MultiSet is
  the sum of the gradings of its elements.

Example:

>>> grading $ MS.fromList [1, 2, 3]
3
>>> grading $ MS.fromList [MS.fromList [1, 2], MS.fromList [3, 4]]
4
-}
instance (Graded a) => Graded (MS.MultiSet a) where
    grading = grading . MS.toList

{- |
  The tuple of two elements is used to represent the tensor product
  in @Symbolics.hs@. The grading of a tuple is the sum of the gradings
  of its elements.

Example:

>>> grading (1, 2)
2
>>> grading ((1, 2), (3, 4))
4
-}
instance (Graded a, Graded b) => Graded (a, b) where
    grading (a, b) = grading a + grading b

-- | A list in which the gradings of the elements is non-decreasing.
newtype NonDecreasingList a = NDecList {unNDecList :: [a]} deriving (Eq)

instance (Show a) => Show (NonDecreasingList a) where
    show (NDecList l) = "NonDecreasingList " ++ show l

instance Foldable NonDecreasingList where
    foldr f z (NDecList l) = foldr f z l

{- |
  Construct a graded list by checking that the grading is
  non-decreasing.

Example:

>>> nDecList ["x", "xy", "xy", "xyz"]
NonDecreasingList ["x","xy","xy","xyz"]
>>> nDecList ["x", "xy", "xyz", "xy"]
NonDecreasingList ["x","xy"*** Exception: The list given to @gradedList@ is not graded.
...
-}
nDecList :: (Graded a) => [a] -> NonDecreasingList a
nDecList [] = NDecList []
nDecList [x] = NDecList [x]
nDecList (x : y : t) =
    if grading x <= grading y
        then ndAppend x $ nDecList (y : t)
        else error "The list given to @gradedList@ is not graded."
  where
    ndAppend x' = NDecList . (x' :) . unNDecList

-- | A list in which all elements have the same grading.
type HomoList a = [a]

{- |
  Groups the elements of a non-decreasing list by their grading.
  With the smallest grading given by @k@.

  Note that if the list starts with an element of grading smaller
  than @k@, the function will hang.

Example:

>>> groupByGradingFrom 1 $ nDecList ["x", "y", "xy", "xy", "yz", "zx", "xyz", "zxy"]
[["x","y"],["xy","xy","yz","zx"],["xyz","zxy"]]
-}
groupByGradingFrom
    :: (Graded a)
    => Integer
    -> NonDecreasingList a
    -> [HomoList a]
groupByGradingFrom _ (NDecList []) = []
groupByGradingFrom k (NDecList l) = case span ((== k) . grading) l of
    (pre, post) -> pre : groupByGradingFrom (k + 1) (NDecList post)

{- |
  Same as @groupByGradingFrom@ but uses the grading of the elements
  and starts with grading @0@.

Example:

>>> groupByGrading $ nDecList ["x", "y", "xy", "xy", "yz", "zx", "xyz", "zxy"]
[[],["x","y"],["xy","xy","yz","zx"],["xyz","zxy"]]
-}
groupByGrading :: (Graded a) => NonDecreasingList a -> [HomoList a]
groupByGrading = groupByGradingFrom 0

{- |
  We define the tree structure and the functions to build it and
  flatten it in order to distribute lists of graded elements.
-}
data Tree_ a = T_ [a] [Tree_ a] | Empty_ deriving (Show)

_buildTree :: (Eq a) => Int -> [[a]] -> Tree_ a
_buildTree i ls =
    if [] `elem` ls
        then Empty_
        else
            T_
                (concatMap (take 1) ls)
                ( map
                    (uncurry _buildTree)
                    $ filter (\(_, x) -> [] `notElem` x) droppedByOne
                )
  where
    droppedByOne =
        [ ( j
          , zipWith
                (\k l -> if k == j then drop 1 l else l)
                [1 ..]
                ls
          )
        | j <- [i .. length ls]
        ]

getElementsFromLevel :: Int -> Tree_ a -> [[a]]
getElementsFromLevel _ Empty_ = []
getElementsFromLevel 0 (T_ el _) = [el]
getElementsFromLevel i (T_ _ subtrees) = concatMap (getElementsFromLevel (i - 1)) subtrees

_flattenTree :: (Eq a) => Tree_ a -> [[[a]]]
_flattenTree Empty_ = []
_flattenTree tree_ = takeWhile (/= []) $ map (`getElementsFromLevel` tree_) [0 ..]

{- |
  Cartesian product of lists in which lists can be infinite. It
  works in the following way:
  @distributeLists [[a_1, a_2], [b_1, b_2]]@
  will return:
  @[[a_1, b_1], [a_1, b_2], [a_2, b_1], [a_2, b_2]]@.

Example:

>>> distributeLists [[1, 2], [11, 12], [21, 22]]
[[1,11,21],[2,11,21],[1,12,21],[1,11,22],[2,12,21],[2,11,22],[1,12,22],[2,12,22]]
-}
distributeLists :: (Eq a) => [[a]] -> [[a]]
distributeLists = concat . _flattenTree . _buildTree 1

{- |
  The same as @distributeLists@ but it groups the resulting terms by
  the sums of their indices. It works in the following way:
  @distributeLists [[a_1, a_2, a_3], [b_1, b_2], [c_1, c_2]]@
  will return:
  @[[[a_1,b_1,c_1]],[[a_2,b_1,c_1],[a_1,b_2,c_1],[a_1,b_1,c_2]],
  [[a_3,b_1,c_1],[a_2,b_2,c_1],[a_2,b_1,c_2],[a_1,b_2,c_2]],
  [[a_3,b_2,c_1],[a_3,b_1,c_2],[a_2,b_2,c_2]],[[a_3,b_2,c_2]]]@.

Example:

>>> distributeGradedLists [[1, 2, 3], [11, 12], [21, 22]]
[[[1,11,21]],[[2,11,21],[1,12,21],[1,11,22]],[[3,11,21],[2,12,21],[2,11,22],[1,12,22]],[[3,12,21],[3,11,22],[2,12,22]],[[3,12,22]]]
-}
distributeGradedLists :: (Eq a) => [[a]] -> [[[a]]]
distributeGradedLists = _flattenTree . _buildTree 1
