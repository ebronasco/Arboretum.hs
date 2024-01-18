{-# LANGUAGE ScopedTypeVariables #-}

module RootedTree (
    PRTree (..),
    graftFF,
    graftFT,
    gl,
) where

import Data.List (intersperse)
import Data.List.Split (splitOn)
import Data.Char (digitToInt)
import GradedList
import Output
import Symbolics

-- Planar rooted tree
data PRTree a = PRTree
    { root :: a
    , children :: [PRTree a]
    }
    deriving (Eq)

instance (Show a) => Show (PRTree a) where
    show (PRTree r xs) =
        show r
            ++ ( case xs of
                    [] -> ""
                    _ -> show xs
               )

instance (Texifiable a) => Texifiable (PRTree a) where
    texify t = "\\forest{" ++ (texify_ t) ++ "}"

texify_ (PRTree r xs) =
    "i_"
        ++ (texify r)
        ++ ( case xs of
                [] -> ""
                _ -> "[" ++ (concat $ intersperse "," $ map texify_ xs) ++ "]"
           )

instance (Basis a) => Graded (PRTree a) where
    grading (PRTree r xs) = (grading r) + sum (map grading xs)

instance (Basis a) => Basis (PRTree a)

graftFF :: forall a. (Basis a) => [PRTree a] -> [PRTree a] -> VectorSpace Integer [PRTree a]
graftFF [] [] = basisVector [[]] :: VectorSpace Integer [PRTree a]
graftFF f1 [] = mempty
graftFF [] f2 = basisVector [f2]
graftFF f1 (t:f2) = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm [f11, f12] = (mapV (:[]) $ graftFT f11 t) * (graftFF f12 f2)

graftFT ::(Basis a) => [PRTree a] -> PRTree a -> VectorSpace Integer (PRTree a)
graftFT f (PRTree r ts) = mapV (PRTree r) $ gl f ts

gl :: (Basis a) => [PRTree a] -> [PRTree a] -> VectorSpace Integer [PRTree a]
gl f1 f2 = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm [f11, f12] = (basisVector [f11]) * (graftFF f12 f2)

