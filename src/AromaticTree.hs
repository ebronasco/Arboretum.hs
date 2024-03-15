{-# LANGUAGE TupleSections #-}

module AromaticTree (
    Aroma (Aroma),
) where

import qualified Data.List as L
import qualified Data.MultiSet as MS
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

instance (Show a) => Show (Aroma a) where
    show (Aroma l) = "(" ++ init (tail $ show l) ++ ")"

type ATree a =
    ( MS.MultiSet (Aroma a)
    , RTree a
    )

type AForest a =
    ( MS.MultiSet (Aroma a)
    , MS.MultiSet (RTree a)
    )

graft
    :: (Ord a)
    => AForest a
    -> AForest a
    -> PowerSeries Integer (AForest a)
graft (a1, f1) (a2, f2) = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm (x, y) = vector (a1, MS.empty) * graftX x * graftY y
    graftX x =
        linear (\a -> 1 *^ (MS.map Aroma a, MS.empty)) $
            linear ((1 *^) . nonplanarF) $
                graftFF (planarF x) (planarF $ MS.map unAroma a2)
    graftY y =
        linear (\f -> (MS.empty, f)) $
            linear ((1 *^) . nonplanarF) $
                graftFF (planarF y) (planarF f2)
