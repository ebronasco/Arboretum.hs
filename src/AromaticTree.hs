{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

module AromaticTree (
    Aroma (Aroma),
    graftOnAroma,
    graftOnMultiAroma,
) where

import qualified Data.List as L
import qualified Data.MultiSet as MS
import Data.Maybe (fromJust)
import Output
import GradedList
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

instance (Graded a) => Graded (Aroma a) where
    grading (Aroma l) = sum $ map grading l

instance (Texifiable a, Eq a) => Texifiable (Aroma (PRTree a)) where
    texify (Aroma l) = "\\forest{(" ++ (L.intercalate "," $ map bracketNotation l) ++ ")}"
      where
        bracketNotation = init . fromJust . L.stripPrefix "\\forest{" . texify

type APTree a =
    ( [Aroma a]
    , PRTree a
    )

type APForest a =
    ( [Aroma a]
    , [PRTree a]
    )

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
graftOnMultiAroma f [] = vector Zero
graftOnMultiAroma f (a:ma) = linear perCoproductTerm $ tensorCoproduct f
  where
    perCoproductTerm (x, y) = (linear (: []) $ x `graftOnAroma` a) * (y `graftOnMultiAroma` ma)
