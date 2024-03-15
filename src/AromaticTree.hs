module AromaticTree (
  Aroma(Aroma),
) where

import qualified Data.List as L
import qualified Data.MultiSet as MS

import RootedTree

newtype Aroma a = Aroma [a]

instance Eq a => Eq (Aroma a) where
  (Aroma a) == (Aroma b) = a `L.elem` circulate b
    where
      circulate :: [a] -> [[a]]
      circulate [] = [[]]
      circulate l = take (length l) $ map (take (length l)) (L.tails (cycle l))

instance Show a => Show (Aroma a) where
  show (Aroma l) = "(" ++ init (tail $ show l) ++ ")"

type AromaticTree a = (MS.MultiSet (Aroma a), MS.MultiSet (RootedTree a))
