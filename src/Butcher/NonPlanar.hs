{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

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
    Tree (..),
    Planarable (..),
) where

import Butcher.Planar
import Butcher.Tree
import Core.Algebra
import Core.GradedList
import Core.Output
import Core.VectorSpace
import qualified Data.MultiSet as MS

{- $setup
  Non-Planar Integer Tree From Brackets
>>> npitfb str = fromBrackets str :: Tree Integer

  Non-Planar Integer Forest From Brackets
>>> npiffb str = fromBrackets str :: MS.MultiSet (Tree Integer)

  Integer Tree From Brackets
>>> itfb str = fromBrackets str :: PlanarTree Integer

  Integer Forest From Brackets
>>> iffb str = fromBrackets str :: [PlanarTree Integer]
-}

---------------------------------------------------------------------

-- * Non-planar trees

---------------------------------------------------------------------

{- | Non-planar trees are represented as a tree with a root and a
multiset of branches which are non-planar trees themselves.
-}
data Tree d = T
    { nonplanarRoot :: d
    , nonplanarBranches :: MS.MultiSet (Tree d)
    }
    deriving (Eq)

instance IsDecorated (Tree d) where
    type Decoration (Tree d) = d

{- |
  @Tree@ is an instance of @IsTree@ and inherits all the relevant
  functions defined in @Tree@ module.

  For more examples see instance of @IsTree (PlanarTree d)@ in @Planar@ module.
-}
instance (Ord d, Graded d) => IsTree (Tree d) where
    root = nonplanarRoot
    branches = MS.toAscList . nonplanarBranches
    buildTree r = T r . MS.fromList

instance (Ord d, Graded d) => HasBracketNotation (Tree d) where
    toBracketsWith = treeToBracketsWith
    fromBracketsWith = treeFromBracketsWith

instance (Show d, Ord d, Graded d) => Texifiable (Tree d) where
    texify = treeTexify

instance (Show d, Ord d, Graded d) => Show (Tree d) where
    show = toBrackets

instance (Eq d, Ord d, Graded d) => IsVector (Tree d) where
    type VectorScalar (Tree d) = Integer
    type VectorBasis (Tree d) = Tree d

    vector = vector . (1 *^)

{- |
  Order on decorations induces an order on trees where we first
  compare the root decorations and then the branches according to
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

---------------------------------------------------------------------

-- * Relate non-planar forests to planar forests

---------------------------------------------------------------------

class Planarable t where
    type Planar t

    nonplanar :: Planar t -> t
    planar :: t -> Planar t

{- |
  Choose a canonical planar representation of a non-planar forest to
  get a planar forest or forget the order of trees and branches in a
  forest to get a non-planar forest.

Examples:

>>> planar $ npiffb "1[2,3],4"
[1[2,3],4]
>>> a = nonplanar $ iffb "1[2,3],4" :: MS.MultiSet (Tree Integer)
>>> b = nonplanar $ iffb "4,1[3,2]"
>>> a == b
True
-}
instance (Ord t, Planarable t) => Planarable (MS.MultiSet t) where
    type Planar (MS.MultiSet t) = [Planar t]

    nonplanar = MS.fromList . map nonplanar
    planar = map planar . MS.toList

{- |
  Apply @planar@ and @nonplanar@ to both components of a pair.

Examples:

>>> f1 = (iffb "1[2,3]",iffb "4,5")
>>> f2 = (iffb "1[3,2]",iffb "5,4")
>>> f1 == f2
False
>>> nonplanar f1 == (nonplanar f2 :: (MS.MultiSet (Tree Integer), MS.MultiSet (Tree Integer)))
True
>>> af1 = (npiffb "1[2,3]",npiffb "4,5")
>>> planar af1
([1[2,3]],[4,5])
>>> af2 = (npiffb "1[3,2]",npiffb "5,4")
>>> planar af2
([1[2,3]],[4,5])
-}
instance (Planarable a, Planarable b) => Planarable (a, b) where
    type Planar (a, b) = (Planar a, Planar b)

    nonplanar (x, y) = (nonplanar x, nonplanar y)
    planar (x, y) = (planar x, planar y)

{- |
  Choose a canonical planar representation of a non-planar tree to get
  a planar tree or forget the order of branches in a planar tree to
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

instance (Ord t, IsVector t, IsTree t) => CanConnesKreimer (MS.MultiSet t) where
    connesKreimer ms = case MS.toList ms of
        [] -> vector (MS.empty, MS.empty)
        [t] -> vector (MS.singleton t, MS.empty) + linear perTerm (connesKreimer $ MS.fromList $ branches t)
          where
            perTerm (f1, f2) = (f1, MS.singleton $ buildTree c $ MS.toList f2)
            c = root t
        f -> morphism (connesKreimer . MS.singleton) $ vector f
