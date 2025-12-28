{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

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
module TensorAlgebra (
    deshuffle,
    Planarable (..),
) where

import qualified Data.MultiSet as MS

import Core.Symbolics
import Core.GradedList


{- |
  Takes a product of basis elements and returns a tensor product of
  the corresponding basis vectors.

Examples:

>>> deshuffle "xyz"
(1 *^ ("","xyz") + 1 *^ ("x","yz") + 1 *^ ("z","xy") + 1 *^ ("y","xz") + 1 *^ ("xz","y") + 1 *^ ("xy","z") + 1 *^ ("yz","x") + 1 *^ ("xyz",""))_3
-}
deshuffle
    :: ( Eq a
       , Graded a
       , IsVector a
       , Num (VectorScalar a)
       , Eq (VectorScalar a)
       , IsVector v
       , VectorScalar v ~ VectorScalar a
       , VectorBasis v ~ [a]
       )
    => v
    -> Vector (VectorScalar a) ([a], [a])
deshuffle = morphism (\b -> 1 *^ (mempty, [b]) +: 1 *^ ([b], mempty) +: Zero) . vector


class Planarable t where
    type Planar t

    nonplanar :: Planar t -> t
    planar :: t -> Planar t

{- |
  Choose a canonical planar representation of a non-planar forest to
  get a planar forest or forget the order of trees and children in a
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
    type Planar (MS.MultiSet t) =  [Planar t]

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

