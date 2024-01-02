module GradedList (
    Grading,
    Graded,
    grading,
    gradingFunction,
    functionFromAssocList,
    bijections,
    unorderedEqualityOfLists,
    distributeGradedLists,
    groupByGrading,
) where

import qualified Data.List as L (
    delete,
    permutations,
 )

-- a list of elements with the same grading
type Grading t = [t]

class Graded t where
    grading :: t -> Int
    grading = checkNonnegative . gradingFunction
      where
        checkNonnegative i =
            if i < 0
                then (error $ "Grading cannot be negative: " ++ (show i))
                else i

    gradingFunction :: t -> Int

instance (Graded a) => Graded (k, a) where
    gradingFunction (_, x) = gradingFunction x

functionFromAssocList :: (Eq a) => [(a, b)] -> (a -> b)
functionFromAssocList assocList x = snd $ head $ filter ((== x) . fst) assocList

bijections :: (Eq a) => [a] -> [b] -> [a -> b]
bijections a b = map functionFromAssocList $ map (\(x, y) -> zip x y) $ zip (repeat a) (L.permutations b)

unorderedEqualityOfLists :: (Eq a) => [a] -> [a] -> Bool
unorderedEqualityOfLists xs ys
    | length xs /= length ys = False -- different length
    | foldr (\t acc -> L.delete t acc) ys xs == [] = True -- same length and xs subset of ys
    | otherwise = False

-- Graded distribution of lists graded by position

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

_flattenTree :: (Eq a) => Tree_ a -> [[a]]
_flattenTree Empty_ = []
_flattenTree tree_ = concat $ takeWhile (/= []) $ map (\i -> getElementsFromLevel i tree_) [0 ..]

distributeLists :: (Eq a) => [[a]] -> [[a]]
distributeLists = _flattenTree . (_buildTree 1)

distributeGradedLists :: (Eq a, Graded a) => [[Grading a]] -> [[Grading a]]
distributeGradedLists = (groupByGradingWith listGrading) . (concatMap distributeLists) . distributeLists
  where
    listGrading = sum . (map grading)

-- break a graded list into the list of gradings
groupByGrading :: (Graded a) => [a] -> [Grading a]
groupByGrading = groupByGradingWith grading

groupByGradingWith :: (a -> Int) -> [a] -> [Grading a]
groupByGradingWith = groupByGradingWith' 0

groupByGradingWith' :: Int -> (a -> Int) -> [a] -> [Grading a]
groupByGradingWith' _ _ [] = []
groupByGradingWith' k f l@(h : _) =
    if (f h) == k
        then
            ( (\(g, t) -> g : (groupByGradingWith' (k + 1) f t)) $
                span (\x -> (f x) == k) l
            )
        else [] : (groupByGradingWith' (k + 1) f l)
