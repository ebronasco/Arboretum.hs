{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : AromaticTree
Description : Implementation of non-planar aromatic trees, forests, their grafting, divergence, and substitution.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental
-}
module AromaticTree (
    Cycle (Cycle),
    divergence,
    Aromatic,
) where

import Control.Monad.State (evalState, get, put)
import Data.Bifunctor (bimap, second)
import qualified Data.List as L
import Data.Maybe (fromJust)
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics
import SyntacticTree

{- $setup
  Non-Planar Integer Tree From Brackets
>>> npitfb str = fromBrackets read str :: Tree Integer

  Aromatic Integer Forest From Brackets
>>> aiffb st = fromBrackets read st :: Aromatic (Tree Integer)
-}

----------------------------------------------------------------------

-- * Cycles

----------------------------------------------------------------------

{- |
  Orbit of a list under cyclic permutation.

Examples:

>>> circulate [1, 2, 3]
[[1,2,3],[2,3,1],[3,1,2]]
>>> circulate [1, 2, 3, 4]
[[1,2,3,4],[2,3,4,1],[3,4,1,2],[4,1,2,3]]
-}
circulate :: [a] -> [[a]]
circulate [] = [[]]
circulate l =
    take (length l) $
        map (take (length l)) (L.tails (cycle l))

-- | A cycle is a list of elements up to cyclic permutation.
newtype Cycle a = Cycle {unCycle :: [a]}

{- |
  Check if two cycles are equal up to cyclic permutation.

Examples:

>>> Cycle [1, 2, 3] == Cycle [3, 1, 2]
True
>>> Cycle [1, 2, 3] == Cycle [3, 2, 1]
False
-}
instance (Eq a) => Eq (Cycle a) where
    (Cycle a) == (Cycle b) = a `elem` circulate b

{- |
  Compare two cycles by comparing the maximums of their cyclic
  permutation orbits.

Examples:

>>> compare (Cycle [1, 2, 3]) (Cycle [3, 1, 2])
EQ
>>> compare (Cycle [1, 3, 2]) (Cycle [3, 1, 2])
GT
-}
instance (Ord a) => Ord (Cycle a) where
    compare (Cycle a) (Cycle b) = compare (maximum $ circulate a) (maximum $ circulate b)

instance Functor Cycle where
    fmap f (Cycle l) = Cycle $ map f l

instance (Show a) => Show (Cycle a) where
    show (Cycle l) = "(" ++ init (tail $ show l) ++ ")"

instance (Graded a) => Graded (Cycle a) where
    grading (Cycle l) = sum $ map grading l

instance
    ( IsVector a
    , Num (VectorScalar a)
    , Eq (VectorScalar a)
    , Eq a
    , Graded a
    )
    => IsVector (Cycle a)
    where
    type VectorScalar (Cycle a) = VectorScalar a
    type VectorBasis (Cycle a) = Cycle a

    vector = vector . (1 *^)

----------------------------------------------------------------------

-- * Divergence

----------------------------------------------------------------------

{- |
  Compute the list of all pairs of an element and the rest of the list.

Examples:

>>> elemComp [1, 2, 3]
[(1,[2,3]),(2,[1,3]),(3,[1,2])]
-}
elemComp :: [a] -> [(a, [a])]
elemComp [] = []
elemComp (x : xs) = (x, xs) : map (second (x :)) (elemComp xs)

{- |
  Build forests along the paths from the root to the vertices.

Examples:

>>> branchPaths $ npitfb "1[2,3]"
[[1[2,3]],[1[3],2],[1[2],3]]
>>> branchPaths $ npitfb "1[2[3],4]"
[[1[2[3],4]],[1[4],2[3]],[1[4],2,3],[1[2[3]],4]]
-}
branchPaths :: (IsTree t) => t -> [[t]]
branchPaths t = [t] : recurs (map (second $ buildTree (root t)) $ elemComp $ children t)
  where
    recurs = concatMap (\(x, y) -> map (y :) (branchPaths x))

type PlanarAromatic t =
    ( [Cycle t]
    , [t]
    )

{- |
  Compute the divergence of a planar aromatic tree by connecting the
  root to the vertices.

Examples:

>>> divergence $ ([], [npitfb "1[2,3]"])
(1 *^ ([(1[2,3])],[]) + 1 *^ ([(1[3],2)],[]) + 1 *^ ([(1[2],3)],[]))_3
>>> divergence $ ([], [npitfb "1[2[3],4]"])
(1 *^ ([(1[2[3],4])],[]) + 1 *^ ([(1[4],2[3])],[]) + 1 *^ ([(1[4],2,3)],[]) + 1 *^ ([(1[2[3]],4)],[]))_4
>>> divergence $ ([Cycle [T 1 MS.empty]], [T 1 MS.empty])
(1 *^ ([(1[1])],[]) + 1 *^ ([(1),(1)],[]))_2
>>> divergence ([Cycle [T 1 MS.empty]], [npitfb "1[2,3]"])
(1 *^ ([(1[1[2,3]])],[]) + 1 *^ ([(1[2,3]),(1)],[]) + 1 *^ ([(1[3],2),(1)],[]) + 1 *^ ([(1[2],3),(1)],[]))_4
>>> divergence ([],[npitfb "1[2,3]", npitfb "4"])
(1 *^ ([],[4[1[2,3]]]) + 1 *^ ([(1[2,3])],[4]) + 1 *^ ([(1[3],2)],[4]) + 1 *^ ([(1[2],3)],[4]))_4
-}
divergence
    :: ( IsDecorated t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       )
    => PlanarAromatic t
    -> Vector (VectorScalar t) (PlanarAromatic t)
divergence (ma, t : ts) = (([], [t]) `graft` (ma, ts)) + linear ((,ts) . (: ma)) (divergenceT t)
  where
    divergenceT t = mconcat $ map (vector . Cycle) $ branchPaths t

----------------------------------------------------------------------

-- * Grafting

----------------------------------------------------------------------

{- |
  Graft a planar rooted forest onto a multi-aroma.

Examples:

>>> graftOnMultiAroma [T 1 MS.empty] [Cycle [T 1 MS.empty, T 1 MS.empty]]
(2 *^ [(1,1[1])])_3
>>> graftOnMultiAroma [T 1 MS.empty] [Cycle [T 1 MS.empty, T 2 MS.empty]]
(1 *^ [(1,2[1])] + 1 *^ [(1[1],2)])_3
>>> graftOnMultiAroma [T 1 MS.empty, T 2 MS.empty] [Cycle [T 1 MS.empty, T 2 MS.empty]]
(1 *^ [(1,2[1,2])] + 1 *^ [(1[1],2[2])] + 1 *^ [(1[2],2[1])] + 1 *^ [(1[1,2],2)])_4
>>> graftOnMultiAroma [T 1 MS.empty] [Cycle [T 1 MS.empty, T 1 MS.empty], Cycle [T 1 MS.empty, T 2 MS.empty]]
(1 *^ [(1,1),(1,2[1])] + 1 *^ [(1,1),(1[1],2)] + 2 *^ [(1,1[1]),(1,2)])_5
-}
graftOnMultiAroma
    :: ( IsDecorated t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       )
    => [t]
    -> [Cycle t]
    -> Vector (VectorScalar t) [Cycle t]
graftOnMultiAroma [] ma = vector (1 *^ ma)
graftOnMultiAroma _ [] = vector Zero
graftOnMultiAroma f [a] = linear ((1 *^) . (: []) . Cycle) $ (f `graft`) $ unCycle a
graftOnMultiAroma f (a : ma) = linear perCoproductTerm $ deshuffleCoproduct f
  where
    perCoproductTerm (x, y) = (x `graftOnMultiAroma` [a]) * (y `graftOnMultiAroma` ma)

{- |
  Graft two aromatic planar forests.

Examples:

>>> graft ([Cycle [T 1 MS.empty]], [T 1 MS.empty]) ([Cycle [T 1 MS.empty]], [T 1 MS.empty])
(1 *^ ([(1),(1)],[1[1]]) + 1 *^ ([(1),(1[1])],[1]))_4
-}
instance
    ( IsDecorated t
    , Eq (Decoration t)
    , Graded (Decoration t)
    , IsTree t
    , IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    )
    => Graftable (PlanarAromatic t)
    where
    graft (ma1, f1) (ma2, f2) = vector (ma1, []) * linear perCoproductTerm (deshuffleCoproduct f1)
      where
        perCoproductTerm (x, y) = linear (,[]) (x `graftOnMultiAroma` ma2) * linear ([],) (y `graft` f2)

----------------------------------------------------------------------

-- * Aromatic Forest

----------------------------------------------------------------------

type Aromatic t =
    ( MS.MultiSet (Cycle t)
    , MS.MultiSet t
    )

instance (Planarable a, Planarable b) => Planarable (a, b) where
    type Planar (a, b) = (Planar a, Planar b)

    -- \| Apply @planar@ to both components of a pair.
    --
    --    Examples:
    --
    --    >>> at1 = ([aroma [PT 1 []], aroma [PT 2 []]], PT 1 [PT 2 [], PT 3 []])
    --    >>> at2 = ([aroma [PT 2 []], aroma [PT 1 []]], PT 1 [PT 3 [], PT 2 []])
    --    >>> at1 == at2
    --    False
    --    >>> nonplanar at1 == nonplanar at2
    --    True
    --    >>> af1 = ([aroma [PT 1 []], aroma [PT 2 []]], [PT 1 [PT 2 [], PT 3 []]])
    --    >>> af2 = ([aroma [PT 2 []], aroma [PT 1 []]], [PT 1 [PT 3 [], PT 2 []]])
    --    >>> af1 == af2
    --    False
    --    >>> nonplanar af1 == nonplanar af2
    --    True
    --
    nonplanar (x, y) = (nonplanar x, nonplanar y)

    -- \| Apply @planar@ to both components of a pair.
    --
    --    Examples:
    --
    --    >>> planar (MS.fromList [aroma [T 1 MS.empty], aroma [T 2 MS.empty]], T 1 $ MS.fromList [T 2 MS.empty, T 3 MS.empty])
    --    ([(1),(2)],1[2,3])
    --    >>> planar (MS.fromList [aroma [T 1 MS.empty], aroma [T 2 MS.empty]], MS.fromList [T 1 $ MS.fromList [T 2 MS.empty, T 3 MS.empty]])
    --    ([(1),(2)],[1[2,3]])
    --
    planar (x, y) = (planar x, planar y)

instance (IsTree t) => IsDecorated (Cycle t) where
    type Decoration (Cycle t) = Decoration t

instance (IsTree t, HasBracketNotation t) => HasBracketNotation (Cycle t) where
    toBrackets f a = "(" ++ init (tail $ show $ map (toBrackets f) $ unCycle a) ++ ")"

    fromBrackets f = Cycle . (fromBrackets f) . escapeParentheses
      where
        escapeParentheses [] = []
        escapeParentheses str = if head str == '(' && last str == ')' then init $ tail str else str

instance (IsTree t) => IsDecorated (Aromatic t) where
    type Decoration (Aromatic t) = Decoration t

instance (IsTree t, HasBracketNotation t, Ord t) => HasBracketNotation (Aromatic t) where
    toBrackets f (ma, ts) = L.intercalate "," $ (map (toBrackets f) $ MS.toList ma) ++ (map (toBrackets f) $ MS.toList ts)

    fromBrackets f = bimap (MS.fromList . map (fromBrackets f)) (MS.fromList . concatMap (fromBrackets f)) . evalState splitAromasAndTrees
      where
        splitAromasAndTrees = do
            str <- get

            let (forest_str, rest) = break (== '(') str
            let (aroma_str, rest') = break (== ')') rest

            let forest_str' = if (not $ null forest_str) && last forest_str == ','
                                 then init forest_str
                                 else forest_str
            let aroma_str' = aroma_str ++ if null rest' then "" else ")"
            let rest'' = if null rest' then "" else tail rest'
            let rest''' = if (not $ null rest'') && head rest'' == ','
                            then tail rest''
                            else rest''

            put rest'''

            (as, fs) <- case rest''' of
                [] -> return ([], [])
                _ -> splitAromasAndTrees

            let as' = if null aroma_str' then as else (aroma_str' : as)
            let fs' = if null forest_str' then fs else (forest_str' : fs)

            return (as', fs')

----------------------------------------------------------------------

-- * Substitution

----------------------------------------------------------------------

-- ** Mark

data Marked a = Marked {unMarked :: a} | Mark deriving (Eq)

instance (Show a) => Show (Marked a) where
    show (Marked a) = "m" ++ show a
    show Mark = "x"

instance (Graded a) => Graded (Marked a) where
    grading (Marked a) = grading a
    grading Mark = 0

instance (Texifiable a) => Texifiable (Marked a) where
    texify (Marked a) = texify a
    texify Mark = "x"

class Markable a where
    type Marked' a

    mark :: a -> Marked' a
    unmark :: Marked' a -> a

instance (Markable a) => Markable [a] where
    type Marked' [a] = [Marked' a]

    mark = map mark
    unmark = map unmark

instance (Markable a, Markable b) => Markable (a, b) where
    type Marked' (a, b) = (Marked' a, Marked' b)

    mark (a, b) = (mark a, mark b)
    unmark (a, b) = (unmark a, unmark b)

instance
    ( IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , IsTree t
    , Decoration t ~ Marked d
    , Eq d
    , Graded d
    )
    => HasSyntacticTree (PlanarAromatic t)
    where
    syn ([], []) = Node concatOp []
    syn ([Cycle ts], []) = Node traceOp [syn $ ([],) $ (: []) $ breakCycle ts]
      where
        breakCycle [] = buildTree Mark []
        breakCycle (t : ts) = addBranch (breakCycle ts) t
        addBranch b t = buildTree (root t) (b : (children t))
    syn ([], [t]) = case children t of
        [] -> Leaf ([], [t])
        bs -> Node graftOp [syn ([], bs), Leaf ([], [buildTree (root t) []])]
    syn (as, ts) =
        Node concatOp $
            (map (syn . (,[]) . (: [])) as)
                ++ (map (syn . ([],) . (: [])) ts)

traceOp
    :: ( IsTree t
       , Decoration t ~ Marked d
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq d
       , Graded d
       )
    => Operation (PlanarAromatic t)
traceOp = Op "trace" "$Tr$" 1 $
    \[f] -> connectRootToMarked f
  where
    connectRootToMarked (as, t : ts) = case (searchMarkTree (as, t)) of
        Nothing -> searchMarkAroma (as, t)
        Just x -> vector x
    searchMarkTree (as, t) = case (filter ((== buildTree Mark []) . last) $ branchPaths t) of
        [] -> Nothing
        l -> Just $ (,[]) $ (: as) $ Cycle $ init $ head l
    searchMarkAroma (as, t) = substitute ([], [buildTree Mark []]) [([], [t])] (as, [])
