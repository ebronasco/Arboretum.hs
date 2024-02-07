module GradedList (
    Graded,
    grading,
    NonDecreasingList,
    unNDecList,
    nDecList,
    HomoList,
    unHomoList,
    homoList,
    distributeLists,
    distributeGradedLists,
    groupByGrading,
) where

-- | Use @Integer@ since it can be converted to any numeric type using @fromInteger@.
class Graded t where
    grading :: t -> Integer

{- | @Integer@ is used to generate basis elements for testing @Symbolics.hs@. The grading of an integer is the number of digits in its absolute value.

Example:

>>> grading 123
3
>>> grading (-123)
3
-}
instance Graded Integer where
    grading 0 = 0
    grading n = 1 + (grading $ abs_n `div` 10)
      where
        abs_n = abs n

-- | @Char@ can be useful to denote variables like @'x', 'y', 'z'@ when using @Symbolics.hs@. The grading of a character is 1.
instance Graded Char where
    grading _ = 1

{- | The Haskell list structure is used to represent the free product in @Symbolics.hs@. The grading of a list is the sum of the gradings of its elements.

Example:

>>> grading [1, 2, 3]
3
>>> grading [[1, 2], [3, 4]]
4
-}
instance (Graded a) => Graded [a] where
    grading [] = 0
    grading (h : t) = (grading h) + (grading t)

-- | A list in which the gradings of the elements is non-decreasing.
newtype NonDecreasingList a = NDecList {unNDecList :: [a]} deriving (Eq)

instance (Show a) => Show (NonDecreasingList a) where
    show (NDecList l) = "NonDecreasingList " ++ show l

instance Functor NonDecreasingList where
    fmap f (NDecList l) = NDecList $ map f l

instance Foldable NonDecreasingList where
    foldr f z (NDecList l) = foldr f z l

{- | Construct a graded list by checking that the grading is non-decreasing.

Example:

>>> nDecList [1, 10, 10, 100]
NonDecreasingList [1,10,10,100]
>>> nDecList [1, 10, 100, 10]
NonDecreasingList [1,10*** Exception: The list given to @gradedList@ is not graded.
...
-}
nDecList :: (Graded a) => [a] -> NonDecreasingList a
nDecList [] = NDecList []
nDecList [x] = NDecList [x]
nDecList (x : y : t) =
    if (grading x) <= (grading y)
        then (ndAppend x $ nDecList (y : t))
        else error "The list given to @gradedList@ is not graded."
  where
    ndAppend x' = NDecList . (x' :) . unNDecList

-- | A list in which all elements have the same grading.
newtype HomoList a = HomoList {unHomoList :: [a]} deriving (Eq)

instance (Show a) => Show (HomoList a) where
    show (HomoList l) = "HomoList " ++ show l

instance Functor HomoList where
    fmap f (HomoList l) = HomoList $ map f l

instance Foldable HomoList where
    foldr f z (HomoList l) = foldr f z l

{- | Construct a grading list by checking that the gradings of the elements are the same.

Example:

>>> homoList [1, 2, 3, 4]
HomoList [1,2,3,4]
>>> homoList [1, 2, 3, 10]
HomoList [1,2*** Exception: The elements of the list given to @homoList@ have different gradings.
...
-}
homoList :: (Graded a) => [a] -> HomoList a
homoList [] = HomoList []
homoList [x] = HomoList [x]
homoList (x : y : t) =
    if (grading x) == (grading y)
        then (homoAppend x $ homoList (y : t))
        else error "The elements of the list given to @homoList@ have different gradings."
  where
    homoAppend x' = HomoList . (x' :) . unHomoList

-- | Groups the elements of a non-decreasing list by their grading. With the smallest grading given by @k@.
groupByGradingWith :: (Graded a) => Integer -> NonDecreasingList a -> [HomoList a]
groupByGradingWith _ (NDecList []) = []
groupByGradingWith k (NDecList l) =
    ( (\(g, t) -> (homoList g) : (groupByGradingWith (k + 1) $ NDecList t)) $
        span (\x -> (grading x) == k) l
    )

{- | Same as @groupByGradingWith@ but uses the grading of the elements and starts with grading @0@.

Example:

>>> groupByGrading $ nDecList [3, 1, 2, 10, 10, 12, 20, 201, 200]
[HomoList [],HomoList [3,1,2],HomoList [10,10,12,20],HomoList [201,200]]
-}
groupByGrading :: (Graded a) => NonDecreasingList a -> [HomoList a]
groupByGrading = groupByGradingWith 0

data Tree_ a = T_ [a] [Tree_ a] | Empty_ deriving (Show)

_buildTree :: (Eq a) => Int -> [[a]] -> Tree_ a
_buildTree i ls =
    if [] `elem` ls
        then Empty_
        else
            ( T_
                (concatMap (take 1) ls)
                ( map
                    (\(j, x) -> _buildTree j x)
                    $ filter (\(_, x) -> not $ [] `elem` x)
                    $ droppedByOne
                )
            )
  where
    droppedByOne =
        [ ( j
          , map
                (\(k, l) -> if k == j then drop 1 l else l)
                $ zip [1 ..] ls
          )
        | j <- [i .. length ls]
        ]

getElementsFromLevel :: Int -> Tree_ a -> [[a]]
getElementsFromLevel _ Empty_ = []
getElementsFromLevel 0 (T_ el _) = [el]
getElementsFromLevel i (T_ _ subtrees) = concat $ map (getElementsFromLevel (i - 1)) subtrees

_flattenTree :: Eq a => Tree_ a -> [[[a]]]
_flattenTree Empty_ = []
_flattenTree tree_ = takeWhile (/= []) $ map (\i -> getElementsFromLevel i tree_) [0 ..]

{- | Cartesian product of lists in which lists can be infinite. It works in the following way:
@distributeLists [[a_1, a_2], [b_1, b_2]]@ will return:
@[[a_1, b_1], [a_1, b_2], [a_2, b_1], [a_2, b_2]]@.

Example:

>>> distributeLists [[1, 2], [11, 12], [21, 22]]
[[1,11,21],[2,11,21],[1,12,21],[1,11,22],[2,12,21],[2,11,22],[1,12,22],[2,12,22]]
-}
distributeLists :: Eq a => [[a]] -> [[a]]
distributeLists = concat . _flattenTree . (_buildTree 1)

{- | The same as @distributeLists@ but it groups the resulting terms by the sums of their indices. It works in the following way:
@distributeLists [[a_1, a_2, a_3], [b_1, b_2], [c_1, c_2]]@ will return:
@[[[a_1,b_1,c_1]],[[a_2,b_1,c_1],[a_1,b_2,c_1],[a_1,b_1,c_2]],[[a_3,b_1,c_1],[a_2,b_2,c_1],[a_2,b_1,c_2],[a_1,b_2,c_2]],[[a_3,b_2,c_1],[a_3,b_1,c_2],[a_2,b_2,c_2]],[[a_3,b_2,c_2]]]@.

Example:

>>> distributeGradedLists [[1, 2, 3], [11, 12], [21, 22]]
[[[1,11,21]],[[2,11,21],[1,12,21],[1,11,22]],[[3,11,21],[2,12,21],[2,11,22],[1,12,22]],[[3,12,21],[3,11,22],[2,12,22]],[[3,12,22]]]
-}
distributeGradedLists :: Eq a => [[a]] -> [[[a]]]
distributeGradedLists = _flattenTree . (_buildTree 1)
