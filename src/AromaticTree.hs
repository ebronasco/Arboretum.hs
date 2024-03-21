{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module AromaticTree (
    Aroma (Aroma),
    graftOnAroma,
    graftOnMultiAroma,
    graftAF,
    elemComp,
    branchPaths,
    divergenceT,
    divergenceAT,
    nonplanarAF,
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

-- | An aroma is a list of elements up to cyclic permutation.
newtype Aroma a = Aroma {unAroma :: [a]}

{- | Check if two aromas are equal up to cyclic permutation.

Examples:

>>> Aroma [1, 2, 3] == Aroma [3, 1, 2]
True
>>> Aroma [1, 2, 3] == Aroma [3, 2, 1]
False
-}
instance (Eq a) => Eq (Aroma a) where
    (Aroma a) == (Aroma b) = a `L.elem` circulate b
      where
        circulate :: [a] -> [[a]]
        circulate [] = [[]]
        circulate l =
            take (length l) $
                map (take (length l)) (L.tails (cycle l))

instance (Ord a) => Ord (Aroma a) where
    compare (Aroma a) (Aroma b) = compare a b

instance Functor Aroma where
    fmap f (Aroma l) = Aroma $ map f l

instance (Show a) => Show (Aroma a) where
    show (Aroma l) = "(" ++ init (tail $ show l) ++ ")"

instance (Graded a) => Graded (Aroma a) where
    grading (Aroma l) = sum $ map grading l

-- * Planar aromatic forests

-- Relies on the fact that @texify@ of @PRTree@ is @\\forest{...}@.
instance (Texifiable a, Eq a) => Texifiable (Aroma (PRTree a)) where
    texify (Aroma l) = "\\forest{(" ++ L.intercalate "," (map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

-- | A planar aromatic tree is a pair of a list of aromas and a planar rooted tree.
type APTree a =
    ( [Aroma (PRTree a)]
    , PRTree a
    )

-- | A planar aromatic forest is a pair of a list of aromas and a list of planar rooted trees.
type APForest a =
    ( [Aroma (PRTree a)]
    , [PRTree a]
    )

-- * Grafting

{- | Graft a planar rooted forest onto a planar aroma.

Examples:

>>> graftOnAroma [PRTree 1 []] (Aroma [PRTree 1 [], PRTree 1 []])
(2 *^ (1,1[1]))_3
>>> graftOnAroma [PRTree 1 []] (Aroma [PRTree 1 [], PRTree 2 []])
(1 *^ (1,2[1]) + 1 *^ (1[1],2))_3
>>> graftOnAroma [PRTree 1 [], PRTree 2 []] (Aroma [PRTree 1 [], PRTree 2 []])
(1 *^ (1,2[1,2]) + 1 *^ (1[1],2[2]) + 1 *^ (1[2],2[1]) + 1 *^ (1[1,2],2))_4
-}
graftOnAroma
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> Aroma (PRTree a)
    -> PowerSeries Integer (Aroma (PRTree a))
graftOnAroma f = linear ((1 *^) . Aroma) . (f `graftFF`) . unAroma

{- | Graft a planar rooted forest onto a multi-aroma.

Examples:

>>> graftOnMultiAroma [PRTree 1 []] [Aroma [PRTree 1 [], PRTree 1 []], Aroma [PRTree 1 [], PRTree 2 []]]
(1 *^ [(1,1),(1,2[1])] + 1 *^ [(1,1),(1[1],2)] + 2 *^ [(1,1[1]),(1,2)])_5
-}
graftOnMultiAroma
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> [Aroma (PRTree a)]
    -> PowerSeries Integer [Aroma (PRTree a)]
graftOnMultiAroma [] ma = vector (1 *^ ma)
graftOnMultiAroma _ [] = vector Zero
graftOnMultiAroma f (a : ma) = linear perCoproductTerm $ tensorCoproduct f
  where
    perCoproductTerm (x, y) = linear (: []) (x `graftOnAroma` a) * (y `graftOnMultiAroma` ma)

{- | Graft two aromatic planar forests.

Examples:

>>> graftAF ([Aroma [PRTree 1 []]], [PRTree 1 []]) ([Aroma [PRTree 1 []]], [PRTree 1 []])
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

>>> branchPaths (PRTree 1 [PRTree 2 [], PRTree 3 []])
[[1[2,3]],[1[3],2],[1[2],3]]
>>> branchPaths (PRTree 1 [PRTree 2 [PRTree 3 []], PRTree 4 []])
[[1[2[3],4]],[1[4],2[3]],[1[4],2,3],[1[2[3]],4]]
-}
branchPaths :: PRTree a -> [[PRTree a]]
branchPaths t@(PRTree r cts) = [t] : recurs (map (second $ PRTree r) $ elemComp cts)
  where
    recurs = concatMap (\(x, y) -> map (y :) (branchPaths x))

{- | Compute the divergence of a planar rooted tree by connecting the root to the vertices.

Examples:

>>> divergenceT (PRTree 1 [PRTree 2 [], PRTree 3 []])
(1 *^ (1[2,3]) + 1 *^ (1[3],2) + 1 *^ (1[2],3))_3
>>> divergenceT (PRTree 1 [PRTree 2 [PRTree 3 []], PRTree 4 []])
(1 *^ (1[2[3],4]) + 1 *^ (1[4],2[3]) + 1 *^ (1[4],2,3) + 1 *^ (1[2[3]],4))_4
-}
divergenceT :: (Eq a, Graded a) => PRTree a -> PowerSeries Integer (Aroma (PRTree a))
divergenceT t = vector $ fromListS $ map ((1 *^) . Aroma) $ branchPaths t

{- | Compute the divergence of a planar aromatic tree by connecting the root to the vertices.

Examples:

>>> divergenceAT ([Aroma [PRTree 1 []]], PRTree 1 [])
(1 *^ [(1[1])] + 1 *^ [(1),(1)])_2
>>> divergenceAT ([Aroma [PRTree 1 []]], PRTree 1 [PRTree 2 [], PRTree 3 []])
(1 *^ [(1[1[2,3]])] + 1 *^ [(1[2,3]),(1)] + 1 *^ [(1[3],2),(1)] + 1 *^ [(1[2],3),(1)])_4
-}
divergenceAT :: (Eq a, Graded a) => APTree a -> PowerSeries Integer [Aroma (PRTree a)]
divergenceAT (ma, t) = ([t] `graftOnMultiAroma` ma) + linear (: ma) (divergenceT t)

-- * Non-planar aromatic forests

-- Relies on the fact that @texify@ of @RTree@ is @\\forest{...}@.
instance (Texifiable a, Eq a, Ord a) => Texifiable (Aroma (RTree a)) where
    texify (Aroma l) = "\\forest{(" ++ L.intercalate "," (map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

type AForest a =
    ( MS.MultiSet (Aroma (RTree a))
    , MS.MultiSet (RTree a)
    )

{- | Forget the order of aromas and all rooted trees involved.

Examples:

>>> af1 = ([Aroma [PRTree 1 []], Aroma [PRTree 2 []]], [PRTree 1 [PRTree 2 [], PRTree 3 []]])
>>> af2 = ([Aroma [PRTree 2 []], Aroma [PRTree 1 []]], [PRTree 1 [PRTree 3 [], PRTree 2 []]])
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
nonplanarAF (ma, f) = (MS.fromList $ map (fmap nonplanarT) ma, nonplanarF f)

{- | Choose a canonical planar representation of an aromatic forest.

Examples:

>>> planarAF (MS.fromList [Aroma [RTree 1 MS.empty], Aroma [RTree 2 MS.empty]], MS.fromList [RTree 1 $ MS.fromList [RTree 2 MS.empty, RTree 3 MS.empty]])
([(1),(2)],[1[2,3]])
-}
planarAF
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => AForest a
    -> APForest a
planarAF (ma, f) = (map (fmap planarT) $ MS.toList ma, planarF f)
