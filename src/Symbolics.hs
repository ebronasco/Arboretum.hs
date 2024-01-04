{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{- |
Module      : Symbolics
Description : Symbolic algebra in Haskell using graded vector spaces.
Copyright   : (c) Eugen Bronasco, 2024
License     : MIT
Maintainer  : ebronasco@gmail.com
Stability   : experimental

An implementation of symbolic algebra using graded vector spaces with the aim of being able to represent and manipulate algebras over the vector spaces of graphs.
-}
module Symbolics (
    Term,
    Scalar,
    Basis,
    scalar,
    basisElement,
    basisTerm,
    scale,
    term,
    VectorSpace (Vector),
    vector,
    vectorG,
    basisVector,
    basisVectorG,
    terms,
    linear,
    flattenV,
    lengthV,
    takeWhileV,
    filterV,
    takeV,
    TensorProduct (TensorProduct),
    lengthTP,
    zipProductWith,
    productMorphism,
    TensorAlgebra,
    algebraMorphism,
    addTerm,
    unVector
) where

import Data.Group
import qualified Data.List as L (
    intercalate,
    sortBy,
 )
import GradedList (
    Graded,
    Grading,
    distributeGradedLists,
    grading,
    gradingFunction,
    groupByGrading,
 )

-- $setup
-- >>> import Test.QuickCheck (Arbitrary (arbitrary), Gen)
-- >>> import Test.QuickCheck.Function (Fun (Fun), apply)
-- >>> :{
-- instance Arbitrary (VectorSpace (Int, Int)) where
--    arbitrary = vector <$> (arbitrary :: Gen [(Int, Int)])
-- :}

--------------------------------------------------------------------------------
-- * Graded vector space
--------------------------------------------------------------------------------

-- | A term of a sum that forms a vector. Contains a scalar and a basis element.
class
    ( Num (Scalar t)
    , Eq (Scalar t)
    , Show (Scalar t)
    , Eq (Basis t)
    , Show (Basis t)
    , Graded t
    ) =>
    Term t
    where
    -- | Set the scalar type. Must be a @Num@, @Eq@, and @Show@.
    type Scalar t

    -- | Set the basis type. Must be an @Eq@ and @Show@.
    type Basis t

    -- | Projections of the term to the scalar and basis types.
    scalar :: t -> Scalar t

    basisElement :: t -> Basis t

    -- | Injection of the basis type into the term type.
    basisTerm :: Basis t -> t
    basisTerm = term (fromInteger 1)

    -- | Scale a term by a scalar.
    scale :: Scalar t -> t -> t
    scale k x = term (k * (scalar x)) (basisElement x)

    -- | Construct a term from a scalar and a basis element.
    term :: Scalar t -> Basis t -> t
    term k x = scale k $ basisTerm x

    {-# MINIMAL scalar, basisElement, (basisTerm, scale | term) #-}

-- | The canonical implementation of a term.
instance
    ( Num k
    , Eq k
    , Show k
    , Eq a
    , Show a
    , Graded a
    )
    => Term (k, a)
    where
    type Scalar (k, a) = k
    type Basis (k, a) = a
    term = (,)
    scalar = fst
    basisElement = snd


{- | 
    Vectors are nested lists of terms. The outer list is @[l0, l1, l2, ..]@ 
    where @li@ is a list of terms with grading @i@.

    NOT OPTIMAL: a vector with a single term with grading @N@ will have @N - 1@ empty lists in it.
    Note: list are used because graphs are not @Ord@ and lists can be infinite.
-}
data VectorSpace t = Vector {unVector :: [Grading t]}

-- | A flat list of terms.
-- Examples:
--
-- >>> terms $ Vector [[], [(1, 1), (1, 2)]]
-- [(1,1),(1,2)]
--
-- Properties:
-- 
-- prop> terms (Vector ts) == concat ts
terms :: VectorSpace t -> [t]
terms = concat . unVector

-- | Only finite vectors can be compared.
instance (Term t) => Eq (VectorSpace t) where
    v1 == v2 = (== 0) $ lengthV $ (<> v2) $ invert v1

-- | The grading of a vector is the grading of its smallest element. If the vector is empty, the grading is @0@.
instance (Graded t) => Graded (VectorSpace t) where
    gradingFunction v = case terms v of
        [] -> 0
        t : _ -> grading t

instance (Show t) => Show (VectorSpace t) where
    show v = "(" ++ (L.intercalate " + " $ map show $ terms v) ++ ")"

-- | Internal function. Adds a term to a finite list. Grading ignorant.
--
-- Examples:
--
-- >>> addTerm (1, 1) [(1, 1), (1, 2)] :: [(Int, Int)]
-- [(2,1),(1,2)]
-- >>> addTerm (1, 3) [(1, 1), (1, 2)] :: [(Int, Int)]
-- [(1,3),(1,1),(1,2)]
--
-- Properties:
--
-- prop> (length $ addTerm t l) - 1 <= length (l :: [(Int, Int)])
--
addTerm :: (Term t) => t -> [t] -> [t]
addTerm t ts = case (span findTerm ts) of
    (pre, []) -> t : pre
    (pre, t0 : post) -> pre ++ (addToTerm t0) ++ post
  where
    findTerm t0 = (basisElement t0) /= (basisElement t)
    addToTerm t0 =
        if scalarSum /= 0
            then [term scalarSum $ basisElement t]
            else []
      where
        scalarSum = (scalar t) + (scalar t0)

-- | Group terms with the same basis element. Grading ignorant.
--
-- Examples:
--
-- >>> groupTerms [(1, 1), (1, 2), (1, 1), (1, 2)] :: [(Int, Int)]
-- [(2,1),(2,2)]
-- >>> groupTerms [(1, 1), (1, 2), (1, 1), (1, 2), (1, 3)] :: [(Int, Int)]
-- [(2,1),(2,2),(1,3)]
--
-- Properties:
--
-- prop> (length $ groupTerms l) <= length (l :: [(Int, Int)])
--
groupTerms :: (Term t) => [t] -> [t]
groupTerms = foldr addTerm mempty

-- | Construct a vector from a list of terms. The list must be finite.
--
-- Examples:
--
-- >>> vector [(1, 1), (1, 2), (1, 1), (1, 2)] :: VectorSpace (Int, Int)
-- ((2,1) + (2,2))
-- >>> vector [(1, 1), (1, 2), (1, 1), (-1, 2), (1, 3)] :: VectorSpace (Int, Int)
-- ((2,1) + (1,3))
--
vector :: (Term t) => [t] -> VectorSpace t
vector = vectorG . (L.sortBy compareGrading)
  where
    compareGrading x y = compare (grading x) (grading y)

-- |  Construct a vector from a list of terms. The list must be graded with finite number of terms having the same grading. The list itself may be infinite.
--
-- Examples:
--
-- >>> vectorG [(1, 1), (1, 2), (1, 1), (1, 2)] :: VectorSpace (Int, Int)
-- ((2,1) + (2,2))
-- >>> takeV 10 $ vectorG [(1, i) | i <- [1..]] :: VectorSpace (Int, Int)
-- ((1,1) + (1,2) + (1,3) + (1,4) + (1,5) + (1,6) + (1,7) + (1,8) + (1,9) + (1,10))
--
vectorG :: (Term t) => [t] -> VectorSpace t
vectorG = Vector . (map groupTerms) . groupByGrading

-- | The same as @vector@ but with basis elements instead of terms.
basisVector :: (Term t) => [Basis t] -> VectorSpace t
basisVector = vector . (map basisTerm)

-- | The same as @vectorG@ but with basis elements instead of terms.
basisVectorG :: (Term t) => [Basis t] -> VectorSpace t
basisVectorG = vectorG . (map basisTerm)

-- | Vector space is a semigroup with addition as the operation.
--
-- Examples:
--
-- >>> vector [(1, 1), (1, 2)] <> (vector [(1, 1), (1, 2), (2, 3)]) :: VectorSpace (Int, Int)
-- ((2,3) + (2,1) + (2,2))
--
-- Properties:
--
-- prop> v1 <> v2 == (v2 <> v1 :: VectorSpace (Int, Int))
--
instance (Term t) => Semigroup (VectorSpace t) where
    v1 <> v2 = Vector $ zipWithDefault addGradings (unVector v1) (unVector v2)
      where
        zipWithDefault _ [] [] = []
        zipWithDefault f [] (e : t) = (f [] e) : zipWithDefault f [] t
        zipWithDefault f (e : t) [] = (f e []) : zipWithDefault f t []
        zipWithDefault f (e1 : t1) (e2 : t2) = (f e1 e2) : zipWithDefault f t1 t2

        addGradings ts1 ts2 = foldr addTerm ts1 ts2

-- | Vector space is a monoid with addition as the operation and the empty vector as the identity.
--
-- Examples:
--
-- >>> mempty :: VectorSpace (Int, Int)
-- ()
-- >>> vector [(1, 1), (1, 2)] <> mempty :: VectorSpace (Int, Int)
-- ((1,1) + (1,2))
--
-- Properties:
--
-- prop> v <> mempty == (v :: VectorSpace (Int, Int))
--
instance (Term t) => Monoid (VectorSpace t) where
    mempty = Vector []

-- | Vector space is a group with addition as the operation and negation as the inverse.
--
-- Examples:
--
-- >>> invert $ vector [(1, 1), (1, 2)] :: VectorSpace (Int, Int)
-- ((-1,1) + (-1,2))
-- >>> vector [(1, 1), (1, 2)] <> invert (vector [(1, 1), (1, 2)]) :: VectorSpace (Int, Int)
-- ()
--
-- Properties:
--
-- prop> v <> invert v == (mempty :: VectorSpace (Int, Int))
-- prop> invert v <> v == (mempty :: VectorSpace (Int, Int))
-- prop> invert (invert v) == (v :: VectorSpace (Int, Int))
--
instance (Term t) => Group (VectorSpace t) where
    invert = fmap $ scale (-1)

-- | Vector space is a functor. The function @f@ must be non-decreasing, i.e. @grading (f t) >= grading t@.
-- TODO: 
-- 1. Current implementation assumes that @f@ preserves the grading. This is not necessary.
--
-- Examples:
--
-- >>> fmap (scale 3) $ vector [(1, 1), (1, 2)] :: VectorSpace (Int, Int)
-- ((3,1) + (3,2))
--
-- Properties:
--
-- prop> fmap id v == (v :: VectorSpace (Int, Int))
--
instance Functor VectorSpace where
    fmap :: (t -> t0) -> VectorSpace t -> VectorSpace t0
    fmap f = Vector . (map $ map f) . unVector

-- | Like @fmap@ but with a function that maps basis elements to basis elements.
--
-- Examples:
-- 
-- >>> linear (^ 2) $ vector [(1,1), (1,2), (1,3), (1,4), (1,5), (1,10) :: (Int, Int)] :: VectorSpace (Int, Int)
-- ((1,1) + (1,4) + (1,9) + (1,16) + (1,25) + (1,100))
--
linear
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> VectorSpace t
    -> VectorSpace t0
linear f = fmap (\t -> term (scalar t) $ f $ basisElement t)

distributeScalar
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       , Basis t ~ VectorSpace t0
       )
    => t
    -> VectorSpace t0
distributeScalar t = fmap (scale $ scalar t) $ basisElement t

flattenV
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       , Basis t ~ VectorSpace t0
       )
    => VectorSpace t
    -> VectorSpace t0
flattenV = mconcat . (map distributeScalar) . terms

lengthV :: VectorSpace t -> Int
lengthV = sum . (map length) . unVector

takeWhileV :: (Graded t) => (t -> Bool) -> VectorSpace t -> VectorSpace t
takeWhileV f = Vector . groupByGrading . (takeWhile f) . concat . unVector

filterV :: (t -> Bool) -> VectorSpace t -> VectorSpace t
filterV f = Vector . (map $ filter f) . unVector

takeV :: (Graded t) => Int -> VectorSpace t -> VectorSpace t
takeV n = Vector . groupByGrading . (take n) . concat . unVector

-- Graded tensor algebra

-- product of terms
data TensorProduct t = TensorProduct (Scalar t) [Basis t]

instance (Eq t, Term t) => Eq (TensorProduct t) where
    (TensorProduct s1 ts1) == (TensorProduct s2 ts2) = (s1 == s2) && (ts1 == ts2)

instance forall t. (Term t) => Graded (TensorProduct t) where
    gradingFunction :: TensorProduct t -> Int
    gradingFunction (TensorProduct _ ts) = sum $ map (grading . t_term) ts
      where
        t_term b = (basisTerm b) :: t

instance (Term t) => Semigroup (TensorProduct t) where
    (TensorProduct s1 ts1) <> (TensorProduct s2 ts2) = TensorProduct (s1 * s2) $ ts1 ++ ts2

instance (Term t) => Monoid (TensorProduct t) where
    mempty = TensorProduct 1 []

lengthTP :: TensorProduct t -> Int
lengthTP (TensorProduct _ ts) = length ts

zipProductWith
    :: ( Term t2
       , Scalar t0 ~ Scalar t1
       , Scalar t0 ~ Scalar t2
       )
    => (Basis t0 -> Basis t1 -> Basis t2)
    -> TensorProduct t0
    -> TensorProduct t1
    -> TensorProduct t2
zipProductWith f (TensorProduct s1 ts1) (TensorProduct s2 ts2) =
    TensorProduct (s1 * s2) $ zipWith f ts1 ts2

productMorphism
    :: ( Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> TensorProduct t
    -> TensorProduct t0
productMorphism f (TensorProduct s ts) = TensorProduct s $ map f ts

instance (Term t) => Show (TensorProduct t) where
    show (TensorProduct s ts) = (show s) ++ " " ++ (L.intercalate " * " $ map show ts)

-- product of terms is a term
instance (Term t) => Term (TensorProduct t) where
    type Scalar (TensorProduct t) = Scalar t
    type Basis (TensorProduct t) = [Basis t]

    term = TensorProduct

    scalar (TensorProduct s _) = s
    basisElement (TensorProduct _ v) = v

type TensorAlgebra t = VectorSpace (TensorProduct t)

instance (Term t, Eq t) => Num (TensorAlgebra t) where
    (+) = (<>)

    (Vector ts1) * (Vector ts2) = Vector $ map (map mconcat) distributed
      where
        distributed = distributeGradedLists [ts1, ts2]

    abs = id

    signum _ = 1

    fromInteger i = Vector [[TensorProduct (fromInteger i) []]]

    negate = invert

algebraMorphism
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> TensorAlgebra t
    -> TensorAlgebra t0
algebraMorphism f = linear $ map f
