{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Algebra
Description : 
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

-}
module Core.Algebra (
    HasMorphism (..),
    CanDeshuffle (..),
    shuffle,
    deconcatenate,
    morphism,
    morphismGraded,
    morphismNonDec,
) where

import qualified Data.MultiSet as MS
import Data.List (inits, tails)

import Core.VectorSpace
import Core.GradedList


---------------------------------------------------------------------

-- * Algebra functions

---------------------------------------------------------------------

class (Foldable f, IsVector v) => HasMorphism f func a v | func -> a v where
    morphism' :: func -> Vector k (f a) -> Vector k (VectorBasis v)

instance {-# OVERLAPABLE #-} ( IsVector v
                   , VectorScalar v ~ k
                   , VectorBasis v ~ b
                   , Monoid b
                   , Functor f
                   , Foldable f
                   , Eq (f a)
                   ) => HasMorphism f (a -> v) a v
    where
    morphism' = morphism

instance {-# OVERLAPPABLE #-} ( IsVector v
                   , VectorScalar v ~ k
                   , VectorBasis v ~ b
                   , Monoid b
                   , Functor f
                   , Foldable f
                   , Eq (f a)
                   ) => HasMorphism f (GradedFunc a v) a v
    where
    morphism' = morphismGraded

instance {-# OVERLAPPABLE #-} ( IsVector v
                   , VectorScalar v ~ k
                   , VectorBasis v ~ b
                   , Monoid b
                   , Functor f
                   , Foldable f
                   , Eq (f a)
                   ) => HasMorphism f (NonDecFunc a v) a v
    where
    morphism' = morphismNonDec

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
    => GradedFunc a v
    -> Vector k (f a)
    -> Vector k b
morphismGraded (GradedFunc f) = linearGraded $ GradedFunc $ product . fmap (vector . f)

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
    => NonDecFunc a v
    -> Vector k (f a)
    -> Vector k b
morphismNonDec (NonDecFunc f) = linearNonDec $ NonDecFunc $ product . fmap (vector . f)




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

shuffle
    :: ( IsVector v
       , Graded v
       )
    => [v] -> [v] -> Vector (VectorScalar v) [v]
shuffle [] l = vector l
shuffle l [] = vector l
shuffle l1@(x1 : xs1) l2@(x2 : xs2) =
    vector [x1] * shuffle xs1 l2
        + vector [x2] * shuffle l1 xs2

deconcatenate
    :: ( IsVector v 
       , Graded v 
       )
    => [v] -> Vector (VectorScalar v) ([v], [v])
deconcatenate [] = vector ([], [])
deconcatenate l = vectorFromList $ map (1 *^) $ zip (inits l) (tails l)


