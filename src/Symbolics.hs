{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
    terms,
    linear,
    flattenV,
    lengthV,
    takeWhileV,
    filterV,
    takeV,
    TensorProduct (TensorProduct),
    productMorphism,
    TensorAlgebra,
    algebraMorphism,
    -- for debug
    unVector,
    addTerm,
    groupTerms,
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

-- TODO:

-- * find a way to extend a map f : Basis t -> Basis t0 to a linear map and a morphism.

-- X leave `addTerm` grading-ignorant.

-- X represent VectorSpace t as a list of lists by grading, [grading 0, grading 1, ..., grading k, ...]

--      where "grading k" is a set of terms t with grading t = k.
--      This way you don't need to call groupByGrading all the time.

-- use list because the graphs are not Ord and lists can be infinite
-- Scalars t must be Num, Eq
-- Basis t must be Num, Eq
-- Term must be Graded
-- VectorSpace is a Group, Functor
-- Product is a Monoid, Functor
-- TensorProduct := VectorSpace (Product t) is Num, Functor

-- Graded vector space

-- minimal complete definition: Scalar t, Basis t, scalar, basisElement, (basisTerm, scale | term)
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
    type Scalar t
    type Basis t

    scalar :: t -> Scalar t
    basisElement :: t -> Basis t

    basisTerm :: Basis t -> t
    basisTerm = term (fromInteger 1)

    scale :: Scalar t -> t -> t
    scale k x = term (k * (scalar x)) (basisElement x)

    term :: Scalar t -> Basis t -> t
    term k x = scale k $ basisTerm x

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

-- vectors represented as a list of gradings of terms
-- NOT OPTIMAL: a vector with a single graph with grading N will have N - 1 empty lists in it
-- SOLUTION: replace [[t]] by [(grading :: Integer, terms :: [t])]
--          more optimal, but harded to implement. Left for later.
data VectorSpace t = Vector {unVector :: [Grading t]}

-- Graded list of terms.
terms :: VectorSpace t -> [t]
terms = concat . unVector

instance (Eq t) => Eq (VectorSpace t) where
    v1 == v2 = (unVector v1) == (unVector v2)

-- grading of a vector is the grading of its smallest element
instance (Graded t) => Graded (VectorSpace t) where
    gradingFunction = grading . head . terms

instance (Show t) => Show (VectorSpace t) where
    show v = "(" ++ (L.intercalate " + " $ map show $ terms v) ++ ")"

-- internal function. Adds a term to the vector. Grading ignorant.
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

-- group terms with the same basis element. Grading ignorant.
groupTerms :: (Term t) => [t] -> [t]
groupTerms = foldr addTerm mempty

-- for finite, non-graded lists
vector :: (Term t) => [t] -> VectorSpace t
vector = vectorG . (L.sortBy compareGrading)
  where
    compareGrading x y = compare (grading x) (grading y)

-- for infinite, graded lists with finite gradings
vectorG :: (Term t) => [t] -> VectorSpace t
vectorG = Vector . (map groupTerms) . groupByGrading

instance (Term t) => Semigroup (VectorSpace t) where
    v1 <> v2 = Vector $ zipWithDefault addGradings (unVector v1) (unVector v2)
      where
        zipWithDefault _ [] [] = []
        zipWithDefault f [] (e : t) = (f [] e) : zipWithDefault f [] t
        zipWithDefault f (e : t) [] = (f e []) : zipWithDefault f t []
        zipWithDefault f (e1 : t1) (e2 : t2) = (f e1 e2) : zipWithDefault f t1 t2

        addGradings ts1 ts2 = foldr addTerm ts1 ts2

instance (Term t) => Monoid (VectorSpace t) where
    mempty = Vector []

instance (Term t) => Group (VectorSpace t) where
    invert = fmap $ scale (-1)

instance Functor VectorSpace where
    fmap f = Vector . (map $ map f) . unVector

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

algebraDerivation
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> TensorAlgebra t
    -> TensorAlgebra t0
algebraDerivation f = flattenV . (linear (vector . listDerivation f))
  where
    listDerivation f [] = []
    listDerivation f (t : ts) = ((f t) : ts) : (map (t :) $ listDerivation f ts)
