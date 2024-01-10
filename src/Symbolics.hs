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
    Scalar,
    Basis,
    scalar,
    basisElement,
    basisTerm,
    scale,
    term,

    -- * Graded vector space
    VectorSpace,
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

    -- * Tensor algebra
    TensorProduct,
    tensorProduct,
    basisTensorProduct,
    lengthTP,
    zipProductWith,
    morphismTP,
    TensorAlgebra,
    morphismTA,

    -- * Symmetric algebra
    SymmetricProduct,
    symmetricProduct,
    basisSymmetricProduct,
    lengthSP,
    morphismSP,
    SymmetricAlgebra,
    morphismSA,

    -- * Debug
    addTerm,
    unVector,
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

{- $setup
>>> :set -XPatternSynonyms
>>> import Test.QuickCheck (Arbitrary (arbitrary), Gen)
>>> import Test.QuickCheck.Function (Fun (Fun), apply, pattern Fn)
>>> :{
instance Arbitrary (VectorSpace Int Int) where
   arbitrary = vector <$> (arbitrary :: Gen [(Int, Int)])
:}

>>> :{
instance Arbitrary (TensorProduct Int Int) where
   arbitrary = TensorProduct <$> (arbitrary :: Gen Int) <*> (arbitrary :: Gen [Int])
:}
-}

-----------------------------------------------------------------------------

-- * Graded vector space

-----------------------------------------------------------------------------

type Term k a = (k, a)

class (Num k, Eq k, Show k) => Scalar k

class (Eq a, Show a, Graded a) => Basis a

term :: (Scalar k, Basis a) => k -> a -> Term k a
term = (,)

scalar :: (Scalar k, Basis a) => Term k a -> k
scalar = fst

basisElement :: (Scalar k, Basis a) => Term k a -> a
basisElement = snd

scale :: (Scalar k, Basis a) => k -> Term k a -> Term k a
scale c1 (c2, x) = (c1 * c2, x)

basisTerm :: (Scalar k, Basis a) => a -> Term k a
basisTerm x = (fromInteger 1, x)

instance (Scalar k, Basis a) => Graded (Term k a) where
    grading = grading . basisElement

{- |
    Vectors are nested lists of terms. The outer list is @[l0, l1, l2, ..]@
    where @li@ is a list of terms with grading @i@.

    /NOT OPTIMAL: a vector with a single term with grading @N@ will have @N - 1@ empty lists in it./

    /Note: list are used because graphs are not @Ord@ and lists can be infinite./
-}
data VectorSpace k a = Vector {unVector :: [Grading (Term k a)]}

{- | A flat list of terms.
Examples:

>>> terms $ Vector [[], [(1, 1), (1, 2)]]
[(1,1),(1,2)]

Properties:

prop> terms (Vector ts) == concat ts
-}
terms :: (Scalar k, Basis a) => VectorSpace k a -> [Term k a]
terms = concat . unVector

-- | Only finite vectors can be compared.
instance (Scalar k, Basis a) => Eq (VectorSpace k a) where
    v1 == v2 = (== 0) $ lengthV $ (<> v2) $ invert v1

instance (Scalar k, Basis a) => Show (VectorSpace k a) where
    show v = "(" ++ (L.intercalate " + " $ map show $ terms v) ++ ")"

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> addTerm (1, 1) [(1, 1), (1, 2)] :: [(Int, Int)]
[(2,1),(1,2)]
>>> addTerm (1, 3) [(1, 1), (1, 2)] :: [(Int, Int)]
[(1,3),(1,1),(1,2)]

Properties:

prop> (length $ addTerm t l) - 1 <= length (l :: [(Int, Int)])
-}
addTerm :: (Scalar k, Basis a) => Term k a -> [Term k a] -> [Term k a]
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

{- | Group terms with the same basis element. Grading ignorant.

Examples:

>>> groupTerms [(1, 1), (1, 2), (1, 1), (1, 2)] :: [(Int, Int)]
[(2,1),(2,2)]
>>> groupTerms [(1, 1), (1, 2), (1, 1), (1, 2), (1, 3)] :: [(Int, Int)]
[(2,1),(2,2),(1,3)]

Properties:

prop> (length $ groupTerms l) <= length (l :: [(Int, Int)])
-}
groupTerms :: (Scalar k, Basis a) => [Term k a] -> [Term k a]
groupTerms = foldr addTerm mempty

{- | Construct a vector from a list of terms. The list must be finite.

Examples:

>>> vector [(1, 1), (1, 2), (1, 1), (1, 2)] :: VectorSpace (Int, Int)
((2,1) + (2,2))
>>> vector [(1, 1), (1, 2), (1, 1), (-1, 2), (1, 3)] :: VectorSpace (Int, Int)
((2,1) + (1,3))
-}
vector :: (Scalar k, Basis a) => [Term k a] -> VectorSpace k a
vector = vectorG . (L.sortBy compareGrading)
  where
    compareGrading x y = compare (grading x) (grading y)

{- |  Construct a vector from a list of terms. The list must be graded with finite number of terms having the same grading. The list itself may be infinite.

Examples:

>>> vectorG [(1, 1), (1, 2), (1, 1), (1, 2)] :: VectorSpace (Int, Int)
((2,1) + (2,2))
>>> takeV 10 $ vectorG [(1, i) | i <- [1..]] :: VectorSpace (Int, Int)
((1,1) + (1,2) + (1,3) + (1,4) + (1,5) + (1,6) + (1,7) + (1,8) + (1,9) + (1,10))
-}
vectorG :: (Scalar k, Basis a) => [Term k a] -> VectorSpace k a
vectorG = Vector . (map groupTerms) . groupByGrading

-- | The same as @vector@ but with basis elements instead of terms.
basisVector :: (Scalar k, Basis a) => [a] -> VectorSpace k a
basisVector = vector . (map basisTerm)

-- | The same as @vectorG@ but with basis elements instead of terms.
basisVectorG :: (Scalar k, Basis a) => [a] -> VectorSpace k a
basisVectorG = vectorG . (map basisTerm)

{- | Vector space is a semigroup with addition as the operation.

Examples:

>>> vector [(1, 1), (1, 2)] <> (vector [(1, 1), (1, 2), (2, 3)]) :: VectorSpace (Int, Int)
((2,3) + (2,1) + (2,2))

Properties:

prop> v1 <> v2 == (v2 <> v1 :: VectorSpace (Int, Int))
-}
instance (Scalar k, Basis a) => Semigroup (VectorSpace k a) where
    v1 <> v2 = Vector $ zipWithDefault addGradings (unVector v1) (unVector v2)
      where
        zipWithDefault _ [] [] = []
        zipWithDefault f [] (e : t) = (f [] e) : zipWithDefault f [] t
        zipWithDefault f (e : t) [] = (f e []) : zipWithDefault f t []
        zipWithDefault f (e1 : t1) (e2 : t2) = (f e1 e2) : zipWithDefault f t1 t2

        addGradings ts1 ts2 = foldr addTerm ts1 ts2

{- | Vector space is a monoid with addition as the operation and the empty vector as the identity.

Examples:

>>> mempty :: VectorSpace (Int, Int)
()
>>> vector [(1, 1), (1, 2)] <> mempty :: VectorSpace (Int, Int)
((1,1) + (1,2))

Properties:

prop> v <> mempty == (v :: VectorSpace (Int, Int))
-}
instance (Scalar k, Basis a) => Monoid (VectorSpace k a) where
    mempty = Vector []

{- | Vector space is a group with addition as the operation and negation as the inverse.

Examples:

>>> invert $ vector [(1, 1), (1, 2)] :: VectorSpace (Int, Int)
((-1,1) + (-1,2))
>>> vector [(1, 1), (1, 2)] <> invert (vector [(1, 1), (1, 2)]) :: VectorSpace (Int, Int)
()

Properties:

prop> v <> invert v == (mempty :: VectorSpace (Int, Int))
prop> invert v <> v == (mempty :: VectorSpace (Int, Int))
prop> invert (invert v) == (v :: VectorSpace (Int, Int))
-}
instance (Scalar k, Basis a) => Group (VectorSpace k a) where
    invert = fmap $ scale (-1)

{- | Extends a function @f@ that maps basis elements to basis elements to a linear map. The resulting function accepts only finite vectors.

Examples:

>>> linear (\b -> b + 1) $ vector [(1, 1), (1, 2), (1, 3), (1, 4)]
((1,2) + (1,3) + (1,4) + (1,5))

Properties:

prop> linear id v == (v :: VectorSpace (Int, Int))

as well as @(linear f (linear g v)) == (linear (f . g) v)@ and @(linear f (v1 <> v2)) == ((linear f v1) <> (linear f v2))@.

/__TODO:__ add property-tests for the last two properties above. Difficulty: how to generate functions that are monotonically increasing with respect to the grading?/
-}
instance (Scalar k) => Functor (VectorSpace k) where
    fmap f = vector . (map $ fmap f) . terms

{- | The same as @fmap@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(grading $ f b1) <= (grading $ f b2)@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 10 $ fmapG (*10) $ (basisVectorG [1..] :: VectorSpace Int Int)
((1,10) + (1,20) + (1,30) + (1,40) + (1,50) + (1,60) + (1,70) + (1,80) + (1,90) + (1,100))
-}
fmapG :: (Scalar k, Basis a, Basis b) => (a -> b) -> VectorSpace k a -> VectorSpace k b
fmapG f = vectorG . (map $ fmap f) . terms

{- | Takes a function from the basis to a vector space and extends it to a linear map. The resulting function accepts only finite vectors.

Examples:

>>> linear (\b -> vector [(1, b), (1, b + 1)]) $ vector [(1, 1), (1, 2), (1, 3), (1, 4)]
((1,1) + (2,2) + (2,3) + (2,4) + (1,5))
-}
linear
    :: ( Scalar k
       , Basis a
       , Basis b
       )
    => (a -> VectorSpace k b)
    -> VectorSpace k a
    -> VectorSpace k b
linear f = vector . (map distributeScalar) . (map $ fmap f) . terms
  where
    distributeScalar t = scale (scalar t) $ basisElement t

{- | The same as @linear@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(grading $ f b1) <= (grading $ f b2)@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 10 $ linearG (\b -> basisVectorG [b..]) $ (basisVectorG [1..] :: VectorSpace Int Int)
((1,1) + (2,2) + (3,3) + (4,4) + (5,5) + (6,6) + (7,7) + (8,8) + (9,9) + (10,10))
-}
linearG
    :: ( Scalar k
       , Basis a
       , Basis b
       )
    => (a -> b)
    -> VectorSpace k a
    -> VectorSpace k b
linearG f = vectorG . (map distributeScalar) . (map $ fmap f) . terms
  where
    distributeScalar t = scale (scalar t) $ basisElement t

{- | Change the coefficients in a vector using a function @f@ that takes the scalar and the basis element of a term and returns a new scalar.

Examples:

>>> renormalize (\s b -> s + 1) $ vector [(1, 1), (1, 2), (1, 3), (1, 4) :: (Int, Int)]
((2,1) + (2,2) + (2,3) + (2,4))
-}
renormalize
    :: ( Scalar k1
       , Scalar k2
       , Basis a
       )
    => (k1 -> a -> k2)
    -> VectorSpace k1 a
    -> VectorSpace k2 a

renormilize f = vectorG . (map renormalizeTerm) . terms
  where
    renormalizeTerm t = term (f (scalar t) (basisElement t)) $ basisElement t

{- | Collapse a vector whose basis and scalars are of the same type to a scalar by summing all terms. The vector must be finite.

Examples:

>>> collapseV $ vector [(1,1), (3,2), (1,3), (5,4)]
30
-}
collapseV :: (Scalar k) => VectorSpace k k -> k
collapseV = sum . (map collapseTerm) . terms
  where
    collapseTerm t = (scalar t) * (basisElement t)

{- | The length of a vector is the number of terms in it.

Examples:

>>> lengthV $ vector [(1,1), (1,2), (1,3), (1,4) :: (Int, Int)]
4

Properties:

prop> lengthV v == length (terms v :: [(Int, Int)])
-}
lengthV :: (Scalar k, Basis a) => VectorSpace k a -> Int
lengthV = sum . (map length) . unVector

{- | Take terms from a vector until the first term that does not satisfy the condition given by @f@.

Examples:

>>> takeWhileV (\(i, j) -> j < 3) $ vector [(1,1), (1,2), (1,3), (1,4) :: (Int, Int)]
((1,1) + (1,2))
>>> takeWhileV (\(i, j) -> j < 5) $ (basisVectorG [1..] :: VectorSpace (Int, Int))
((1,1) + (1,2) + (1,3) + (1,4))

Properties:

prop> takeWhileV (\_ -> True) v == (v :: VectorSpace (Int, Int))
prop> takeWhileV (\_ -> False) v == (mempty :: VectorSpace (Int, Int))
-}
takeWhileV :: (Scalar k, Basis a) => (Term k a -> Bool) -> VectorSpace k a -> VectorSpace k a
takeWhileV f = Vector . groupByGrading . (takeWhile f) . concat . unVector

{- | Filter terms from a vector that satisfy the condition given by @f@.

Examples:

>>> takeV 10 $ filterV (\(_, j) -> j `mod` 3 == 0) $ basisVectorG [1..] :: VectorSpace (Int, Int)
((1,3) + (1,6) + (1,9) + (1,12) + (1,15) + (1,18) + (1,21) + (1,24) + (1,27) + (1,30))

Properties:

prop> filterV (\_ -> True) v == (v :: VectorSpace (Int, Int))
prop> filterV (\_ -> False) v == (mempty :: VectorSpace (Int, Int))
-}
filterV :: (Scalar k, Basis a) => (Term k a -> Bool) -> VectorSpace t -> VectorSpace t
filterV f = Vector . (map $ filter f) . unVector

{- | Take the first @n@ terms from a vector.

Examples:

>>> takeV 10 $ (basisVectorG [1..] :: VectorSpace (Int, Int))
((1,1) + (1,2) + (1,3) + (1,4) + (1,5) + (1,6) + (1,7) + (1,8) + (1,9) + (1,10))

Properties:

prop> takeV (lengthV v) v == (v :: VectorSpace (Int, Int))
prop> takeV 0 v == (mempty :: VectorSpace (Int, Int))
-}
takeV :: (Scalar k, Basis a) => Int -> VectorSpace k a -> VectorSpace k a
takeV n = Vector . groupByGrading . (take n) . concat . unVector

-----------------------------------------------------------------------------

-- * Graded tensor algebra

-----------------------------------------------------------------------------

data TensorProduct k a = TensorProduct k [a]

instance (Eq t, Term t) => Eq (TensorProduct t) where
    (TensorProduct s1 ts1) == (TensorProduct s2 ts2) = (s1 == s2) && (ts1 == ts2)

{- | Construct a tensor product from a list of terms by taking the product of their scalars and the concatenation of their basis elements.

Examples:

>>> tensorProduct [(1, 1), (1, 2), (1, 1), (1, 2)] :: TensorProduct (Int, Int)
1 1 * 2 * 1 * 2
-}
tensorProduct :: (Term t) => [t] -> TensorProduct t
tensorProduct ts = TensorProduct (product $ map scalar ts) $ map basisElement ts

{- | Construct a tensor product from a list of basis elements.

Examples:

>>> basisTensorProduct [1, 2, 1, 2] :: TensorProduct (Int, Int)
1 1 * 2 * 1 * 2
-}
basisTensorProduct :: (Term t) => [Basis t] -> TensorProduct t
basisTensorProduct = tensorProduct . (map basisTerm)

{- | The grading of a tensor product is the sum of the gradings of its terms. If the tensor product is empty, the grading is @0@.

Examples:

>>> grading $ (TensorProduct 1 [1, 2, 1, 2] :: TensorProduct (Int, Int))
4

Properties:

prop> grading (t1 <> t2 :: TensorProduct (Int, Int)) == (grading t1) + (grading t2)
-}
instance forall t. (Term t) => Graded (TensorProduct t) where
    gradingFunction (TensorProduct _ ts) = sum $ map (grading . t_term) ts
      where
        t_term b = (basisTerm b) :: t

instance (Term t) => Semigroup (TensorProduct t) where
    (TensorProduct s1 ts1) <> (TensorProduct s2 ts2) = TensorProduct (s1 * s2) $ ts1 ++ ts2

instance (Term t) => Monoid (TensorProduct t) where
    mempty = TensorProduct 1 []

lengthTP :: TensorProduct t -> Int
lengthTP (TensorProduct _ ts) = length ts

{- | Zip two tensor products with a function that takes two basis elements and returns a basis element.

Examples:

>>> zipProductWith (\b1 b2 -> b1 + b2) (basisTensorProduct [1, 2, 3, 4] :: TensorProduct (Int, Int)) (basisTensorProduct [40, 30, 20, 10] :: TensorProduct (Int, Int)) :: TensorProduct (Int, Int)
1 41 * 32 * 23 * 14
-}
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

{- | Extends a function @f@ that maps basis elements to basis elements to a morphism that respect the tensor product.

Examples:

>>> morphismP (\b -> b + 1) (basisTensorProduct [1, 2, 3, 4] :: TensorProduct (Int, Int)) :: TensorProduct (Int, Int)
1 2 * 3 * 4 * 5
-}
morphismTP
    :: ( Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> TensorProduct t
    -> TensorProduct t0
morphismTP f (TensorProduct s ts) = TensorProduct s $ map f ts

instance (Term t) => Show (TensorProduct t) where
    show (TensorProduct s ts) = (show s) ++ " " ++ (L.intercalate " * " $ map show ts)

instance (Term t) => Term (TensorProduct t) where
    type Scalar (TensorProduct t) = Scalar t
    type Basis (TensorProduct t) = [Basis t]

    term = TensorProduct

    scalar (TensorProduct s _) = s
    basisElement (TensorProduct _ v) = v

-- | A graded tensor algebra is defined as a graded vector space with the tensor product as the term.
type TensorAlgebra t = VectorSpace (TensorProduct t)

{- | Tensor algebra is has an instance of the @Num@ class since both addition and multiplication are defined on it. To ensure that the product of two vectors in the tensor algebra is also in the tensor algebra, the product is distributed over the basis elements of the two vectors.

Examples:

>>> (vector [basisTensorProduct [1, 2], basisTensorProduct [3, 4] :: TensorProduct (Int, Int)] :: TensorAlgebra (Int, Int)) * (vector [basisTensorProduct [11, 12], basisTensorProduct [13, 14] :: TensorProduct (Int, Int)] :: TensorAlgebra (Int, Int))
(1 1 * 2 * 11 * 12 + 1 3 * 4 * 11 * 12 + 1 1 * 2 * 13 * 14 + 1 3 * 4 * 13 * 14)
-}
instance (Term t, Eq t) => Num (TensorAlgebra t) where
    (+) = (<>)

    (Vector ts1) * (Vector ts2) = Vector $ map (map mconcat) distributed
      where
        distributed = distributeGradedLists [ts1, ts2]

    -- \| Absolute value of a vector makes no sense.
    abs = id

    -- \| Signum of a vector makes no sense either.
    signum _ = 1

    -- \| Inject integers into the tensor algebra.
    fromInteger i = Vector [[TensorProduct (fromInteger i) []]]

    negate = invert

{- | Take a function @f@ that maps basis elements to basis elements and extends it to a morphism of the tensor algebra.

Examples:

>>> morphismTP (\b -> b + 1) $ vector [basisTensorProduct [1, 2, 3, 4], basisTensorProduct [11, 12, 13, 14] :: TensorProduct (Int, Int)] :: TensorAlgebra (Int, Int)
(1 2 * 3 * 4 * 5 + 1 12 * 13 * 14 * 15)
-}
morphismTA
    :: ( Term t
       , Term t0
       , Scalar t ~ Scalar t0
       )
    => (Basis t -> Basis t0)
    -> TensorAlgebra t
    -> TensorAlgebra t0
morphismTA f = linear $ map f

-----------------------------------------------------------------------------

-- * Graded symmetric algebra

-----------------------------------------------------------------------------

{- | The @scalar t@ is the multiplicity of the basis element @basisElement t@ in the symmetric product.
                                                    |
-}
data SymmetricProduct t = SymmetricProduct (Scalar t) [t]

instance (Term t) => Eq (SymmetricProduct t) where
    (SymmetricProduct s1 ts1) == (SymmetricProduct s2 ts2) =
        (s1 == s2) && ((vector ts1) == (vector ts2))

{- | Construct a symmetric product from a list of terms by taking the product of their scalars and the concatenation of their basis elements.

Examples:

>>> symmetricProduct [(1, 1), (1, 2), (1, 1), (1, 2), (2, 3)] :: SymmetricProduct (Int, Int)
2 1^2 * 2^2 * 3
-}
symmetricProduct :: (Term t) => [t] -> SymmetricProduct t
symmetricProduct ts =
    scale (product $ map scalar ts) $ basisSymmetricProduct $ map basisElement ts

{- | Construct a symmetric product from a list of basis elements.

Examples:

>>> basisSymmetricProduct [1, 2, 1, 2] :: SymmetricProduct (Int, Int)
1 1^2 * 2^2
-}
basisSymmetricProduct :: (Term t) => [Basis t] -> SymmetricProduct t
basisSymmetricProduct = SymmetricProduct 1 . groupTerms . (map basisTerm)

{- | The grading of a symmetric product is the sum of the gradings of its terms. If the symmetric product is empty, the grading is @0@.

Examples:

>>> grading $ (basisSymmetricProduct [1, 2, 1, 2] :: SymmetricProduct (Int, Int))
4

Properties:

prop> grading (t1 <> t2 :: SymmetricProduct (Int, Int)) == (grading t1) + (grading t2)
-}
instance forall t. (Term t) => Graded (SymmetricProduct t) where
    gradingFunction (SymmetricProduct _ ts) =
        foldr
            (\t acc -> acc + ((scalar t) * (grading t)))
            0
            ts

instance (Term t) => Semigroup (SymmetricProduct t) where
    (SymmetricProduct s1 ts1) <> (SymmetricProduct s2 ts2) =
        SymmetricProduct (s1 * s2) $ terms $ (vector ts1) <> (vector ts2)

instance (Term t) => Monoid (SymmetricProduct t) where
    mempty = SymmetricProduct 1 []

lengthSP :: forall t. (Term t) => SymmetricProduct t -> Int
lengthSP (SymmetricProduct _ ts) = foldr (\t acc -> acc + (scalar t)) 0 ts
