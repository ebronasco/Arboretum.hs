{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module AromaticTree (
    Aroma (Aroma),
    graftOnAroma,
    graftOnMultiAroma,
    graftAF,
    elemComp,
    branchPath,
    divergenceT,
    divergenceAT,
    nonplanarAF,
    planarAF,
) where

import qualified Data.List as L
import Data.Maybe (fromJust)
import Data.Bifunctor (second)
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics

newtype Aroma a = Aroma {unAroma :: [a]}

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

instance (Texifiable a, Eq a) => Texifiable (Aroma (PRTree a)) where
    texify (Aroma l) = "\\forest{(" ++ L.intercalate "," (map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

type APTree a =
    ( [Aroma (PRTree a)]
    , PRTree a
    )

type APForest a =
    ( [Aroma (PRTree a)]
    , [PRTree a]
    )

-- * Grafting

graftOnAroma
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> Aroma (PRTree a)
    -> PowerSeries Integer (Aroma (PRTree a))
graftOnAroma f = linear ((1 *^) . Aroma) . (f `graftFF`) . unAroma

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

graftAF
    :: ( Eq a
       , Graded a
       )
    => APForest a
    -> APForest a
    -> PowerSeries Integer (APForest a)
graftAF (ma1, f1) (ma2, f2) = vector (ma1, []) * linear perCoproductTerm (tensorCoproduct f1)
  where
    perCoproductTerm (x, y) = linear (, []) (x `graftOnMultiAroma` ma2) * linear ([],) (y `graftFF` f2)

-- * Divergence

elemComp :: [a] -> [(a, [a])]
elemComp [] = []
elemComp (x : xs) = (x, xs) : map (second (x :)) (elemComp xs)

branchPath :: PRTree a -> [[PRTree a]]
branchPath t@(PRTree r cts) = [t] : recurs (map (second $ PRTree r) $ elemComp cts)
  where
    recurs = concatMap (\(x, y) -> map (y :) (branchPath x)) 

divergenceT :: (Eq a, Graded a) => PRTree a -> PowerSeries Integer (Aroma (PRTree a))
divergenceT t = vector $ fromListS $ map ((1 *^) . Aroma) $ branchPath t

divergenceAT :: (Eq a, Graded a) => APTree a -> PowerSeries Integer [Aroma (PRTree a)]
divergenceAT (ma, t) = ([t] `graftOnMultiAroma` ma) + linear (:ma) (divergenceT t)

-- * Non-planar aromatic forests

instance (Texifiable a, Eq a, Ord a) => Texifiable (Aroma (RTree a)) where
    texify (Aroma l) = "\\forest{(" ++ L.intercalate "," (map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

type AForest a =
    ( MS.MultiSet (Aroma (RTree a))
    , MS.MultiSet (RTree a)
    )

nonplanarAF
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => APForest a
    -> AForest a
nonplanarAF (ma, f) = (MS.fromList $ map (fmap nonplanarT) ma, nonplanarF f)

planarAF
    :: ( Eq a
       , Graded a
       , Ord a
       )
    => AForest a
    -> APForest a
planarAF (ma, f) = (map (fmap planarT) $ MS.toList ma, planarF f)
