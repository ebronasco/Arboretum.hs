{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : RootedTree
Description : Planar and non-planar trees, forests, and their grafting and substitution.
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the post-Lie algebra of planar trees and
pre-Lie algebra of non-planar trees.
-}
module Butcher.NonPlanar (
    PlanarTree (..),
    Tree (..),
    Graftable,
    graft,
    gl,
) where

import Control.Monad.State
import Data.List (intercalate)
import qualified Data.MultiSet as MS

import Core.GradedList
import Core.Parse
import Core.Output
import Core.Symbolics
import TensorAlgebra

{- $setup
  Integer Tree From Brackets
>>> itfb str = fromBrackets read str :: PlanarTree Integer

  Integer Forest From Brackets
>>> iffb str = fromBrackets read str :: [PlanarTree Integer]

  Non-Planar Integer Tree From Brackets
>>> npitfb str = fromBrackets read str :: Tree Integer

  Non-Planar Integer Forest From Brackets
>>> npiffb str = fromBrackets read str :: MS.MultiSet (Tree Integer)
-}


---------------------------------------------------------------------

-- * Planar trees

---------------------------------------------------------------------

{- | Planar trees are represented as a tree with a root and a list of
children which are planar trees themselves.
-}
data PlanarTree d = PT
    { planarRoot :: d
    , planarChildren :: [PlanarTree d]
    }
    deriving (Eq)

instance IsDecorated (PlanarTree d) where
    type Decoration (PlanarTree d) = d

instance IsTree (PlanarTree d) where
    root = planarRoot
    children = planarChildren

    buildTree = PT

{- |
  Every tree can be written and constructed from a string using
  the bracket notation.

Example:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBrackets f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets read "(1)[(2),3[04,05],(6)]" :: Tree Integer
1[2,3[4,5],6]
-}
instance HasBracketNotation (PlanarTree d) where
    toBrackets f t =
        f (root t)
            ++ ( case children t of
                    [] -> ""
                    _ -> "[" ++ intercalate "," (map (toBrackets f) (children t)) ++ "]"
               )

    fromBrackets decFromStr = evalState (parseTree decFromStr)

{- |
  LaTeX notation for planar trees using @planarforest.py@ TeX package.

Example:

>>> texify $ itfb "1[2,3]"
"\\forest{i_1[i_2,i_3]}"
-}
instance (Show d) => Texifiable (PlanarTree d) where
    texifyID _ = "PlanarTree"
    texify t = "\\forest{" ++ toBrackets wrap t ++ "}"
      where
        wrap r = "i_" ++ filter (/= '"') (show r)

instance (Show d) => Show (PlanarTree d) where
    show = toBrackets show

-- | Planar trees are vectors with integer coefficients.
instance (Eq d, Graded d) => IsVector (PlanarTree d) where
    type VectorScalar (PlanarTree d) = Integer
    type VectorBasis (PlanarTree d) = PlanarTree d

    vector = vector . (1 *^)

{- |
  Grading of a planar tree is the sum of gradings of the nodes.

Example:

>>> grading $ itfb "1[2,34]"
3

Note: the grading of an integer is the number of digits with @0@ having grading @0@.
-}
instance (Graded d) => Graded (PlanarTree d) where
    grading (PT r xs) = grading r + sum (map grading xs)

---------------------------------------------------------------------

-- * Non-planar trees

---------------------------------------------------------------------

{- | Non-planar trees are represented as a tree with a root and a
multiset of children which are non-planar trees themselves.
-}
data Tree d = T
    { nonplanarRoot :: d
    , nonplanarChildren :: MS.MultiSet (Tree d)
    }
    deriving (Eq)

instance IsDecorated (Tree d) where
    type Decoration (Tree d) = d

instance (Ord d) => IsTree (Tree d) where
    root = nonplanarRoot
    children = MS.toAscList . nonplanarChildren

    buildTree r = T r . MS.fromList

{- |
  Every tree can be written and constructed from a string using
  the bracket notation.

Example:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBrackets f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets read "(1)[(2),3[04,05],(6)]" :: Tree Integer
1[2,3[4,5],6]
-}
instance (Ord d) => HasBracketNotation (Tree d) where
    toBrackets f t =
        f (root t)
            ++ ( case children t of
                    [] -> ""
                    _ -> "[" ++ intercalate "," (map (toBrackets f) (children t)) ++ "]"
               )

    fromBrackets decFromStr = evalState (parseTree decFromStr)

{- |
  LaTeX notation for trees using @planarforest.py@ TeX package.

Example:

>>> texify $ itfb "1[2,3]"
"\\forest{i_1[i_2,i_3]}"
-}
instance (Show d, Ord d) => Texifiable (Tree d) where
    texifyID _ = "Tree"
    texify = texify . planar

instance (Show d, Ord d) => Show (Tree d) where
    show = toBrackets show

instance (Eq d, Ord d, Graded d) => IsVector (Tree d) where
    type VectorScalar (Tree d) = Integer
    type VectorBasis (Tree d) = Tree d

    vector = vector . (1 *^)

{- |
  Order on decorations induces an order on trees where we first
  compare the root decorations and then the children according to
  their order.

Example:

>>> compare (npitfb "1") (npitfb "2")
LT
>>> compare (npitfb "1") (npitfb "1[2,3]")
LT
>>> compare (npitfb "1[2]") (npitfb "1[3]")
LT
>>> compare (npitfb "1[2]") (npitfb "1[2]")
EQ
>>> compare (npitfb "1[2,4]") (npitfb "1[2,3]")
GT
-}
instance (Ord d) => Ord (Tree d) where
    compare (T r1 c1) (T r2 c2) = compare (r1, c1) (r2, c2)

instance (Ord d, Graded d) => Graded (Tree d) where
    grading = grading . planar

{- |
  Choose a canonical planar representation of a non-planar tree to get
  a planar tree or forget the order of children in a planar tree to
  get a non-planar tree.

Example:

>>> planar $ npitfb "1[2,3]"
1[2,3]
>>> a =  nonplanar $ itfb "1[2,3]" :: Tree Integer
>>> b =  nonplanar $ itfb "1[3,2]"
>>> a == b
True
-}
instance (Ord d) => Planarable (Tree d) where
    type Planar (Tree d) = PlanarTree d

    nonplanar (PT r xs) = T r (nonplanar xs)
    planar (T r xs) = PT r (planar xs)

---------------------------------------------------------------------

class (IsVector a) => Graftable a where
    graft :: a -> a -> Vector (VectorScalar a) (VectorBasis a)

{- |
  Grafting of two planar forests using the @deshuffleCoproduct@
  function that splits @f1@ into subforests in all possible ways.

Example:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> graft f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5
-}
instance
    ( IsTree t
    , IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Eq (Decoration t)
    , Graded (Decoration t)
    )
    => Graftable [t]
    where
    graft [] [] = vector []
    graft _ [] = vector Zero
    graft [] f2 = vector f2
    graft f [t] = linear ((: []) . buildTree (root t)) $ gl f $ children t
    graft f1 (t : f2) =
        linear perCoproductTerm $ deshuffle f1
      where
        perCoproductTerm (f11, f12) = graft f11 [t] * graft f12 f2

instance
    ( IsTree t
    , IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Ord t
    , Eq (Decoration t)
    , Graded (Decoration t)
    , Ord (Decoration t)
    )
    => Graftable (MS.MultiSet t)
    where
    graft f1 f2 = linear MS.fromList $ graft (MS.toList f1) (MS.toList f2)

{- |
  Grossman-Larson product of two forests.

Example:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> gl f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5
-}
gl
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       )
    => [t]
    -> [t]
    -> Vector (VectorScalar t) [t]
gl f1 f2 = linear perCoproductTerm $ deshuffle f1
  where
    perCoproductTerm (f11, f12) = vector f11 * graft f12 f2
