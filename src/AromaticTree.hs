{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : AromaticTree
Description : Implementation of planar/non-planar aromatic trees, forests, their grafting, and divergence.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental
-}
module AromaticTree (
    Aroma (Aroma),
    graftOnAroma,
    graftOnMultiAroma,
    graftAF,
    elemComp,
    branchPaths,
    divergenceT,
    divergenceAT,
    APTree,
    ATree,
    APForest,
    AForest,
    nonplanarA,
    nonplanarAT,
    nonplanarAF,
    planarA,
    planarAT,
    planarAF,
) where

import Data.Bifunctor (second)
import qualified Data.List as L
import Data.Maybe (fromJust)
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics

{- | Orbit of a list under cyclic permutation.

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

{- | Check if two cycles are equal up to cyclic permutation.

Examples:

>>> Cycle [1, 2, 3] == Cycle [3, 1, 2]
True
>>> Cycle [1, 2, 3] == Cycle [3, 2, 1]
False
-}
instance (Eq a) => Eq (Cycle a) where
    (Cycle a) == (Cycle b) = a `L.elem` circulate b

-- | Compare two cycles by comparing the maximums of their cyclic permutation orbits.
instance (Ord a) => Ord (Cycle a) where
    compare (Cycle a) (Cycle b) = compare (maximum $ circulate a) (maximum $ circulate b)

instance Functor Cycle where
    fmap f (Cycle l) = Cycle $ map f l

instance (Show a) => Show (Cycle a) where
    show (Cycle l) = "(" ++ init (tail $ show l) ++ ")"

instance (Graded a) => Graded (Cycle a) where
    grading (Cycle l) = sum $ map grading l

newtype PAroma a = PAroma {unPAroma :: Cycle (PRTree a)}

instance (Eq a) => Eq (PAroma a) where
    (PAroma a) == (PAroma b) = a == b

instance (Show a) => Show (PAroma a) where
    show (PAroma l) = show l

instance (Graded a) => Graded (PAroma a) where
    grading (PAroma l) = grading l

-- * Planar aromatic forests

-- Relies on the fact that @texify@ of @PRTree@ is @\\forest{...}@.
instance (Show a, Texifiable a, Eq a) => Texifiable (PAroma a) where
    texify (PAroma (Cycle l)) = "\\forest{(" ++ L.intercalate "," (map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

-- | A planar aromatic tree is a pair of a list of aromas and a planar rooted tree.
type APTree a =
    ( [PAroma a]
    , PRTree a
    )

-- | A planar aromatic forest is a pair of a list of aromas and a list of planar rooted trees.
type APForest a =
    ( [PAroma a]
    , [PRTree a]
    )

-- * Grafting

{- | Graft a planar rooted forest onto a planar aroma.

Examples:

>>> graftOnAroma [PRTree 1 []] (PAroma $ Cycle [PRTree 1 [], PRTree 1 []])
(2 *^ (1,1[1]))_3
>>> graftOnAroma [PRTree 1 []] (PAroma $ Cycle [PRTree 1 [], PRTree 2 []])
(1 *^ (1,2[1]) + 1 *^ (1[1],2))_3
>>> graftOnAroma [PRTree 1 [], PRTree 2 []] (PAroma $ Cycle [PRTree 1 [], PRTree 2 []])
(1 *^ (1,2[1,2]) + 1 *^ (1[1],2[2]) + 1 *^ (1[2],2[1]) + 1 *^ (1[1,2],2))_4
-}
graftOnAroma
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> PAroma a
    -> PowerSeries Integer (PAroma a)
graftOnAroma f = linear ((1 *^) . PAroma . Cycle) . (f `graftFF`) . unCycle . unPAroma

{- | Graft a planar rooted forest onto a multi-aroma.

Examples:

>>> graftOnMultiAroma [PRTree 1 []] [PAroma $ Cycle [PRTree 1 [], PRTree 1 []], PAroma $ Cycle [PRTree 1 [], PRTree 2 []]]
(1 *^ [(1,1),(1,2[1])] + 1 *^ [(1,1),(1[1],2)] + 2 *^ [(1,1[1]),(1,2)])_5
-}
graftOnMultiAroma
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> [PAroma a]
    -> PowerSeries Integer [PAroma a]
graftOnMultiAroma [] ma = vector (1 *^ ma)
graftOnMultiAroma _ [] = vector Zero
graftOnMultiAroma f (a : ma) = linear perCoproductTerm $ tensorCoproduct f
  where
    perCoproductTerm (x, y) = linear (: []) (x `graftOnAroma` a) * (y `graftOnMultiAroma` ma)

{- | Graft two aromatic planar forests.

Examples:

>>> graftAF ([PAroma $ Cycle [PRTree 1 []]], [PRTree 1 []]) ([PAroma $ Cycle [PRTree 1 []]], [PRTree 1 []])
(1 *^ ([(1),(1)],[1[1]]) + 1 *^ ([(1),(1[1])],[1]))_4
-}
graftAF
    :: ( Eq a
       , Graded a
       )
    => APForest a
    -> APForest a
    -> PowerSeries Integer (APForest a)
graftAF (ma1, f1) (ma2, f2) = vector (ma1, []) * linear perCoproductTerm (tensorCoproduct f1)
  where
    perCoproductTerm (x, y) = linear (,[]) (x `graftOnMultiAroma` ma2) * linear ([],) (y `graftFF` f2)

-- * Divergence

{- | Compute the list of all pairs of an element and the rest of the list.

Examples:

>>> elemComp [1, 2, 3]
[(1,[2,3]),(2,[1,3]),(3,[1,2])]
-}
elemComp :: [a] -> [(a, [a])]
elemComp [] = []
elemComp (x : xs) = (x, xs) : map (second (x :)) (elemComp xs)

{- | Build forests along the paths from the root to the vertices.

Examples:

>>> branchPaths (RTree 1 [RTree 2 [], RTree 3 []])
[[1[2,3]],[1[3],2],[1[2],3]]
>>> branchPaths (RTree 1 [RTree 2 [RTree 3 []], RTree 4 []])
[[1[2[3],4]],[1[4],2[3]],[1[4],2,3],[1[2[3]],4]]
-}
branchPaths :: PRTree a -> [[PRTree a]]
branchPaths t@(PRTree r cts) = [t] : recurs (map (second $ PRTree r) $ elemComp cts)
  where
    recurs = concatMap (\(x, y) -> map (y :) (branchPaths x))

{- | Compute the divergence of a planar rooted tree by connecting the root to the vertices.

Examples:

>>> divergenceT $ nonplanarT (PRTree 1 [PRTree 2 [], PRTree 3 []])
(1 *^ (1[2,3]) + 1 *^ (1[3],2) + 1 *^ (1[2],3))_3
>>> divergenceT $ nonplanarT (PRTree 1 [PRTree 2 [PRTree 3 []], PRTree 4 []])
(1 *^ (1[2[3],4]) + 1 *^ (1[4],2[3]) + 1 *^ (1[4],2,3) + 1 *^ (1[2[3]],4))_4
-}
divergenceT :: (Eq a, Graded a) => PRTree a -> PowerSeries Integer (PAroma a)
divergenceT t = vector $ fromListS $ map ((1 *^) . PAroma . Cycle) $ branchPaths t

{- | Compute the divergence of a planar aromatic tree by connecting the root to the vertices.

Examples:

>>> divergenceAT ([PAroma $ Cycle [PRTree 1 []]], PRTree 1 [])
(1 *^ [(1[1])] + 1 *^ [(1),(1)])_2
>>> divergenceAT ([PAroma $ Cycle [PRTree 1 []]], PRTree 1 [PRTree 2 [], PRTree 3 []])
(1 *^ [(1[1[2,3]])] + 1 *^ [(1[2,3]),(1)] + 1 *^ [(1[3],2),(1)] + 1 *^ [(1[2],3),(1)])_4
-}
divergenceAT :: (Eq a, Graded a) => APTree a -> PowerSeries Integer [PAroma a]
divergenceAT (ma, t) = ([t] `graftOnMultiAroma` ma) + linear (: ma) (divergenceT t)

-- * Non-planar aromatic forests

newtype Aroma a = Aroma {unAroma :: Cycle (RTree a)}

instance (Eq a) => Eq (Aroma a) where
    (Aroma a) == (Aroma b) = a == b

instance (Ord a) => Ord (Aroma a) where
    compare (Aroma a) (Aroma b) = compare a b

instance (Show a) => Show (Aroma a) where
    show (Aroma l) = show l

instance (Graded a, Ord a) => Graded (Aroma a) where
    grading (Aroma l) = grading l



type ATree a =
    ( MS.MultiSet (Aroma a)
    , RTree a
    )

type AForest a =
    ( MS.MultiSet (Aroma a)
    , MS.MultiSet (RTree a)
    )

nonplanarA
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => PAroma a
    -> Aroma a
nonplanarA = Aroma . Cycle . (map nonplanarT) . unCycle . unPAroma

{- | Forget the order of aromas in a multi-aroma.

Examples:

>>> ma1 = [Aroma $ Cycle [PRTree 1 []], Aroma $ Cycle [PRTree 2 []]]
>>> ma2 = [Aroma $ Cycle [PRTree 2 []], Aroma $ Cycle [PRTree 1 []]]
>>> ma1 == ma2
False
>>> nonplanarMA ma1 == nonplanarMA ma2
True
-}
nonplanarMA
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => [PAroma a]
    -> MS.MultiSet (Aroma a)
nonplanarMA = MS.fromList . (map nonplanarA)



{- | Forget the order of aromas and branches of the rooted tree.

Examples:

>>> at1 = ([Aroma $ Cycle [PRTree 1 []], Aroma $ Cycle [PRTree 2 []]], PRTree 1 [PRTree 2 [], PRTree 3 []])
>>> at2 = ([Aroma $ Cycle [PRTree 2 []], Aroma $ Cycle [PRTree 1 []]], PRTree 1 [PRTree 3 [], PRTree 2 []])
>>> at1 == at2
False
>>> nonplanarAT at1 == nonplanarAT at2
True
-}
nonplanarAT
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => APTree a
    -> ATree a
nonplanarAT (ma, t) = (nonplanarMA ma, nonplanarT t)


{- | Forget the order of aromas and all rooted trees involved.

Examples:

>>> af1 = ([Aroma $ Cycle [PRTree 1 []], Aroma $ Cycle [PRTree 2 []]], [PRTree 1 [PRTree 2 [], PRTree 3 []]])
>>> af2 = ([Aroma $ Cycle [PRTree 2 []], Aroma $ Cycle [PRTree 1 []]], [PRTree 1 [PRTree 3 [], PRTree 2 []]])
>>> af1 == af2
False
>>> nonplanarAF af1 == nonplanarAF af2
True
-}
nonplanarAF
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => APForest a
    -> AForest a
nonplanarAF (ma, f) = (nonplanarMA ma, nonplanarF f)

planarA
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => Aroma a
    -> PAroma a
planarA = PAroma . Cycle . (map planarT) . unCycle . unAroma

{- | Choose a canonical planar representation of a multi-aroma.

Examples:

>>> planarMA $ MS.fromList [Aroma $ Cycle [RTree 1 MS.empty], Aroma $ Cycle [RTree 2 MS.empty]]
[(1),(2)]
-}
planarMA
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => MS.MultiSet (Aroma a)
    -> [PAroma a]
planarMA = map planarA . MS.toList


{- | Choose a canonical planar representation of an aromatic tree.

Examples:

>>> planarAT (MS.fromList [Aroma $ Cycle [RTree 1 MS.empty], Aroma $ Cycle [RTree 2 MS.empty]], RTree 1 $ MS.fromList [RTree 2 MS.empty, RTree 3 MS.empty])
([(1),(2)],1[2,3])
-}
planarAT
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => ATree a
    -> APTree a
planarAT (ma, t) = (planarMA ma, planarT t)

{- | Choose a canonical planar representation of an aromatic forest.

Examples:

>>> planarAF (MS.fromList [Aroma $ Cycle [RTree 1 MS.empty], Aroma $ Cycle [RTree 2 MS.empty]], MS.fromList [RTree 1 $ MS.fromList [RTree 2 MS.empty, RTree 3 MS.empty]])
([(1),(2)],[1[2,3]])
-}
planarAF
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => AForest a
    -> APForest a
planarAF (ma, f) = (planarMA ma, planarF f)
