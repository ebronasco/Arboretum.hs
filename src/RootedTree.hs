{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : RootedTree
Description : Planar and non-planar rooted trees and the grafting product.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the post-Lie algebra of planar rooted trees and
pre-Lie algebra of non-planar rooted trees.
-}
module RootedTree (
    PRTree (..),
    graftFF,
    graftFT,
    gl,
    RTree (..),
    nonplanarT,
    nonplanarF,
    planarT,
    planarF,
) where

import Data.List (intercalate)
import qualified Data.MultiSet as MS
import GradedList
import Output
import Symbolics

-- * Planar rooted trees

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
    texifyID _ = "PRTree"
    texify t = "\\forest{" ++ texify_ t ++ "}"

texify_ :: (Texifiable a) => PRTree a -> String
texify_ (PRTree r xs) =
    "i_"
        ++ texify r
        ++ ( case xs of
                [] -> ""
                _ -> "[" ++ intercalate "," (map texify_ xs) ++ "]"
           )

{- | Grading of a planar rooted tree is the sum of gradings of the nodes.

Example:

>>> grading $ PRTree 1 [PRTree 2 [], PRTree 31 []]
4

Note that the grading of an integer is the number of digits.
-}
instance (Graded a) => Graded (PRTree a) where
    grading (PRTree r xs) = grading r + sum (map grading xs)

{- | Grafting of two planar rooted forests using the @tensorCoproduct@ function that splits @f1@ into subforests in all possible ways and @graftFT@ function that grafts forests onto trees.

Example:

>>> graftFF [PRTree 1 [PRTree 2 []]] [PRTree 3 [], PRTree 4 [PRTree 5 []]]
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5
-}
graftFF
    :: forall a
    .  ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> [PRTree a]
    -> PowerSeries Integer [PRTree a]
graftFF [] [] = vector [] :: PowerSeries Integer [PRTree a]
graftFF _  [] = vector Zero
graftFF [] f2 = vector f2
graftFF f1 (t:f2) = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm (f11, f12) = graftFT f11 t * graftFF f12 f2

{- | Graft a forest onto a tree using the Grossman-Larson product implemented by the @gl@ function.

Example:

>>> graftFT [PRTree 1 [PRTree 2 []]] (PRTree 3 [PRTree 4 []])
(1 *^ [3[4[1[2]]]] + 1 *^ [3[1[2],4]])_4
-}
graftFT
    :: ( Eq a
       , Graded a
       ) 
    => [PRTree a]
    -> PRTree a
    -> PowerSeries Integer [PRTree a]
graftFT f (PRTree r ts) = linear ((:[]) . PRTree r) $ gl f ts

{- | Grossman-Larson product of two forests.

Example:

>>> gl [PRTree 1 [PRTree 2 []]] [PRTree 3 [], PRTree 4 [PRTree 5 []]]
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5
-}
gl
    :: ( Eq a
       , Graded a
       )
    => [PRTree a]
    -> [PRTree a]
    -> PowerSeries Integer [PRTree a]
gl f1 f2 = linear perCoproductTerm $ tensorCoproduct f1
  where
    perCoproductTerm (f11, f12) = vector f11 * graftFF f12 f2

-- * Non-planar rooted trees

-- | Non-planar rooted trees are represented as a tree with a root and a multiset of children which are non-planar rooted trees themselves.
data RTree a = RTree 
    { root' :: a
    , children' :: MS.MultiSet (RTree a)
    }
    deriving (Eq)

instance Ord a => Ord (RTree a) where
    compare (RTree r1 c1) (RTree r2 c2) = compare (r1, c1) (r2, c2)

instance (Ord a, Graded a) => Graded (RTree a) where
    grading = grading . planarT

instance (Ord a, Texifiable a) => Texifiable (RTree a) where
    texifyID _ = "RTree"
    texify = texify . planarT

instance (Eq a, Texifiable a) => Texifiable (MS.MultiSet a) where
    texifyID _ = "MultiSet"
    texify = texify . MS.toList
    texifyDebug i j = texifyDebug i j . MS.toList

-- | Brace notation for non-planar rooted trees. Children are enclosed in curly braces.
instance (Show a) => Show (RTree a) where
    show (RTree r xs) =
        show r
            ++ ( case MS.toList xs of
                    [] -> ""
                    _ -> "{" ++ (tail . init . show . MS.toList) xs ++ "}"
               )

{- | Forget the order of children in a planar rooted tree.

Example:

>>> a =  nonplanarT $ PRTree 1 [PRTree 2 [], PRTree 3 []]
>>> b =  nonplanarT $ PRTree 1 [PRTree 3 [], PRTree 2 []]
>>> a == b
True
-}
nonplanarT :: Ord a => PRTree a -> RTree a
nonplanarT (PRTree r xs) = RTree r (nonplanarF xs)

{- | Forget the order of trees and children in a planar rooted forest.

Example:

>>> a = nonplanarF $ [PRTree 1 [PRTree 2 [], PRTree 3 []], PRTree 4 []]
>>> b = nonplanarF $ [PRTree 4 [], PRTree 1 [PRTree 3 [], PRTree 2 []]]
>>> a == b
True
-}
nonplanarF :: Ord a => [PRTree a] -> MS.MultiSet (RTree a)
nonplanarF = MS.fromList . map nonplanarT

{- | Choose a canonical planar representation of a non-planar rooted tree.

Example:

>>> planarT $ RTree 1 (MS.fromList [RTree 2 MS.empty, RTree 3 MS.empty])
1[2,3]
-}

planarT :: Ord a => RTree a -> PRTree a
planarT (RTree r xs) = PRTree r (planarF xs)

{- | Choose a canonical planar representation of a non-planar rooted forest.

Example:

>>> planarF $ MS.fromList [RTree 1 (MS.fromList [RTree 2 MS.empty, RTree 3 MS.empty]), RTree 4 MS.empty]
[1[2,3],4]
-}
planarF :: Ord a => MS.MultiSet (RTree a) -> [PRTree a]
planarF = map planarT . MS.toList
