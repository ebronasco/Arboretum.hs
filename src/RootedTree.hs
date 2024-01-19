{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : PRTree
Description : Planar rooted trees and the grafting product.
Copyright   : (c) Eugen Bronasco, 2024
License     : MIT
Maintainer  : ebronasco@gmail.com
Stability   : experimental

Implementation of the post-Lie algebra of planar rooted trees.
-}
module RootedTree (
    PRTree (..),
    graftFF,
    graftFT,
    gl,
) where

import Data.List (intersperse)
import GradedList
import Output
import Symbolics
import VectorSpace

-- | Planar rooted trees are represented as a tree with a root and a list of children which are planar rooted trees themselves.
data PRTree a = PRTree
    { root :: a
    , children :: [PRTree a]
    }
    deriving (Eq)

{- | Bracket notation for planar rooted trees.

Example:

>>> PRTree 1 [PRTree 2 [], PRTree 3 []]
1[2,3]
-}
instance (Show a) => Show (PRTree a) where
    show (PRTree r xs) =
        show r
            ++ ( case xs of
                    [] -> ""
                    _ -> show xs
               )

{- | LaTeX notation for planar rooted trees using @planarforest.py@ TeX package.

Example:

>>> texify $ PRTree 1 [PRTree 2 [], PRTree 3 []]
"\\forest{i_1[i_2,i_3]}"
-}
instance (Texifiable a) => Texifiable (PRTree a) where
    texify t = "\\forest{" ++ (texify_ t) ++ "}"

texify_ :: (Texifiable a) => PRTree a -> String
texify_ (PRTree r xs) =
    "i_"
        ++ (texify r)
        ++ ( case xs of
                [] -> ""
                _ -> "[" ++ (concat $ intersperse "," $ map texify_ xs) ++ "]"
           )

{- | Grading of a planar rooted tree is the sum of gradings of the nodes.

Example:

>>> grading $ PRTree 1 [PRTree 2 [], PRTree 31 []]
4

Note that the grading of an integer is the number of digits.
-}
instance (Basis a) => Graded (PRTree a) where
    grading (PRTree r xs) = (grading r) + sum (map grading xs)

-- | Planar rooted trees can serve as a basis for a vector space.
instance (Basis a) => Basis (PRTree a)

{- | Grafting of two planar rooted forests using the @tensorCoproduct@ function that splits @f1@ into subforests in all possible ways and @graftFT@ function that grafts forests onto trees.

Example:

>>> graftFF [PRTree 1 [PRTree 2 []]] [PRTree 3 [], PRTree 4 [PRTree 5 []]]
((1,[3[1[2]],4[5]]) + (1,[3,4[1[2],5]]) + (1,[3,4[5[1[2]]]]))
-}
graftFF :: forall a. (Basis a) => [PRTree a] -> [PRTree a] -> VectorSpace Integer [PRTree a]
graftFF [] [] = basisVector [[]] :: VectorSpace Integer [PRTree a]
graftFF _ [] = mempty
graftFF [] f2 = basisVector [f2]
graftFF f1 (t : f2) = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm [f11, f12] = (mapV (: []) $ graftFT f11 t) * (graftFF f12 f2)

{- | Graft a forest onto a tree using the Grossman-Larson product implemented by the @gl@ function.

Example:

>>> graftFT [PRTree 1 [PRTree 2 []]] (PRTree 3 [PRTree 4 []])
((1,3[1[2],4]) + (1,3[4[1[2]]]))
-}
graftFT :: (Basis a) => [PRTree a] -> PRTree a -> VectorSpace Integer (PRTree a)
graftFT f (PRTree r ts) = mapV (PRTree r) $ gl f ts

{- | Grossman-Larson product of two forests.

Example:

>>> gl [PRTree 1 [PRTree 2 []]] [PRTree 3 [], PRTree 4 [PRTree 5 []]]
((1,[1[2],3,4[5]]) + (1,[3[1[2]],4[5]]) + (1,[3,4[1[2],5]]) + (1,[3,4[5[1[2]]]]))
-}
gl :: (Basis a) => [PRTree a] -> [PRTree a] -> VectorSpace Integer [PRTree a]
gl f1 f2 = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm [f11, f12] = (basisVector [f11]) * (graftFF f12 f2)
