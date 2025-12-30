{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

{- |
Module      : Algebra
Description : 
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

-}
module Core.Algebra (
    CanDeshuffle (..),
    IsMonomial (..),
    morphism,
    morphismGraded,
    morphismNonDec,
) where

import qualified Data.MultiSet as MS
import Data.Kind (Constraint)

import Core.VectorSpace
import Core.GradedList

class (Foldable m) => IsMonomial m where
    type MapConstraint m b :: Constraint
    singleton :: a -> m a
    mmap :: MapConstraint m b => (a -> b) -> m a -> m b

instance IsMonomial [] where
    type MapConstraint [] b = ()
    singleton = (:[])
    mmap = map

instance IsMonomial MS.MultiSet where
    type MapConstraint MS.MultiSet b = (Ord b)
    singleton = MS.singleton
    mmap = MS.map

---------------------------------------------------------------------

-- * Algebra functions

---------------------------------------------------------------------

{- |
  Take a function @f@ that maps basis elements to basis elements and
  extends it to a morphism of the algebra.

!!! The function @morphism f@ accepts only finite vectors.

Examples:

>>> f1 x = if x < 9 then 1 *^ [x+1] else 1 *^ [x, 1]
>>> v1 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphism f1 v1
(1 *^ [7,8])_2 + (1 *^ [9,9,1])_3
>>> f2 x = vectorFromList [1 *^ [x], 1 *^ [x+1]]
>>> v2 = vectorFromList [1 *^ [1, 2], 1 *^ [3, 4]]
>>> morphism f2 v2
(1 *^ [1,2] + 1 *^ [2,2] + 1 *^ [1,3] + 1 *^ [2,3] + 1 *^ [3,4] + 1 *^ [4,4] + 1 *^ [3,5] + 1 *^ [4,5])_2
-}
morphism
    :: ( Functor f
       , Foldable f
       , Eq (f a)
       , Monoid b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k (f a)
    -> Vector k b
morphism f = linear $ product . fmap (vector . f)

{- |
  Take a function @f@ that maps basis elements to basis elements and
  extends it to a morphism of the tensor algebra.

!!! The function @f@ must preserve the grading.

Examples:

>>> f1 x = 1 *^ [1,x]
>>> v1 = vectorFromList [1 *^ [6,7], 1 *^ [8, 9]]
>>> morphismGraded f1 v1
*** Exception: Grading mismatch in a list of terms
...
>>> f2 x = 1 *^ [x + 1]
>>> v2 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphismGraded f2 v2
(1 *^ [7,8] + 1 *^ [9,10])_2
>>> v3 = vectorFromNonDecList [i *^ (replicate i 1) | i <- [1..]]
>>> takeV 10 $ morphismGraded f2 v3
(1 *^ [2])_1 + (2 *^ [2,2])_2 + (3 *^ [2,2,2])_3 + (4 *^ [2,2,2,2])_4 + (5 *^ [2,2,2,2,2])_5 + (6 *^ [2,2,2,2,2,2])_6 + (7 *^ [2,2,2,2,2,2,2])_7 + (8 *^ [2,2,2,2,2,2,2,2])_8 + (9 *^ [2,2,2,2,2,2,2,2,2])_9 + (10 *^ [2,2,2,2,2,2,2,2,2,2])_10
-}
morphismGraded
    :: ( Functor f
       , Foldable f
       , Eq (f a)
       , Monoid b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k (f a)
    -> Vector k b
morphismGraded f = linearGraded $ product . fmap (vector . f)

{- |
  Take a function @f@ that maps basis elements to basis elements and
  extends it to a morphism of the tensor algebra.

!!! The function @f@ must be non-decreasing (see @linearNonDec@).

Examples:

>>> f1 x = 1 *^ [x+1]
>>> v1 = vectorFromList [1 *^ [6,7], 1 *^ [8, 9]]
>>> morphismNonDec f1 v1
(1 *^ [7,8] + 1 *^ [9,10])_2
>>> f2 x = if x > 0 && x < 9 then 1*^ [x + 1] else 1 *^ [x]
>>> v2 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphismNonDec f2 v2
(1 *^ [7,8] + 1 *^ [9,9])_2
>>> v3 = vectorFromNonDecList [i *^ (replicate i 1) | i <- [1..]]
>>> takeV 10 $ morphismNonDec f2 v3
(1 *^ [2])_1 + (2 *^ [2,2])_2 + (3 *^ [2,2,2])_3 + (4 *^ [2,2,2,2])_4 + (5 *^ [2,2,2,2,2])_5 + (6 *^ [2,2,2,2,2,2])_6 + (7 *^ [2,2,2,2,2,2,2])_7 + (8 *^ [2,2,2,2,2,2,2,2])_8 + (9 *^ [2,2,2,2,2,2,2,2,2])_9 + (10 *^ [2,2,2,2,2,2,2,2,2,2])_10
-}
morphismNonDec
    :: ( Functor f
       , Foldable f
       , Eq (f a)
       , Monoid b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k (f a)
    -> Vector k b
morphismNonDec f = linearNonDec $ product . fmap (vector . f)




---------------------------------------------------------------------

-- * Common algebras

---------------------------------------------------------------------

class (IsVector a) => CanDeshuffle a where
    deshuffle :: a -> Vector (VectorScalar a) (a, a)

{-
class (Foldable f) => HasSingleton f where
    singleton :: a -> f a

instance HasSingleton [] where
    singleton a = [a]

instance HasSingleton MS.MultiSet where
    singleton a = MS.singleton a
-}

{- |
  Takes a product of basis elements and returns a tensor product of
  the corresponding basis vectors.

Examples:

>>> deshuffle "xyz"
(1 *^ ("","xyz") + 1 *^ ("x","yz") + 1 *^ ("z","xy") + 1 *^ ("y","xz") + 1 *^ ("xz","y") + 1 *^ ("xy","z") + 1 *^ ("yz","x") + 1 *^ ("xyz",""))_3
-}
instance (IsVector a, Graded a) => CanDeshuffle [a]
    where
    deshuffle = morphism (\b -> 1 *^ (mempty, [b]) +: 1 *^ ([b], mempty) +: Zero) . vector

instance (IsVector a, Graded a, Ord a) => CanDeshuffle (MS.MultiSet a)
    where
    deshuffle = (linear fromList') . deshuffle . MS.toList
      where
        fromList' (l1, l2) = 1 *^ (MS.fromList l1, MS.fromList l2)

