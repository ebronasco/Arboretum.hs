module GradedList (
    Grading,
    Graded,
    grading,
    distributeLists,
    distributeGradedLists,
    groupByGrading,
) where

-- a list of elements with the same grading
type Grading t = [t]

-- | Use @Integer@ since it can be converted to any numeric type using @fromInteger@.
class Graded t where
    grading :: t -> Integer

-- | Used for testing purposes.
instance Graded Int where
  grading 0 = 0
  grading n = 1 + (grading $ abs_n `div` 10)
    where
      abs_n = abs n

instance Graded Integer where
  grading 0 = 0
  grading n = 1 + (grading $ abs_n `div` 10)
    where
      abs_n = abs n

instance Graded Char where
  grading _ = 1

instance Graded a => Graded [a] where
  grading [] = 0
  grading (h : t) = (grading h) + (grading t)

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

_flattenTree :: (Eq a) => Tree_ a -> [[[a]]]
_flattenTree Empty_ = []
_flattenTree tree_ = takeWhile (/= []) $ map (\i -> getElementsFromLevel i tree_) [0 ..]

distributeLists :: (Eq a) => [[a]] -> [[a]]
distributeLists = concat . _flattenTree . (_buildTree 1)

distributeGradedLists :: (Eq a) => [[a]] -> [[[a]]]
distributeGradedLists = _flattenTree . (_buildTree 1)

-- break a graded list into the list of gradings
groupByGrading :: (Graded a, Show a) => [a] -> [Grading a]
groupByGrading = groupByGradingWith 0 (fromInteger . grading)

groupByGradingWith :: Show a => Int -> (a -> Int) -> [a] -> [Grading a]
groupByGradingWith _ _ [] = []
groupByGradingWith k f l@(h : _) =
    if (f h) == k
        then
            ( (\(g, t) -> g : (groupByGradingWith (k + 1) f t)) $
                span (\x -> (f x) == k) l
            )
        else if (f h) > k
            then
                [] : (groupByGradingWith (k + 1) f l)
            else error $ "The list given to @groupByGradingWith@ is not graded, therefore, the grading of the element " ++ (show h) ++ " is less than the expected grading " ++ (show k) ++ "."
