{-# LANGUAGE FlexibleInstances #-}

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
    linearG,
    renormalize,
    scaleV,
    functional,
    lengthV,
    takeWhileV,
    filterV,
    takeV,

    -- * Tensor algebra
    TensorAlgebra,
    morphism,

    -- * Debug
    addTerm,
    unVector,
) where

import Data.Group
import qualified Data.List as L (
    intercalate,
    sortBy,
 )
import qualified Data.Monoid as M (
    Product (..),
 )
import GradedList (
    Graded,
    Grading,
    distributeGradedLists,
    grading,
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

instance (Basis a) => Basis [a]

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
    invert = renormalize (\s _ -> negate s)

{- | Extends a function @f@ that maps basis elements to basis elements to a linear map. The resulting function accepts only finite vectors.

Examples:

>>> mapV (\b -> b + 1) $ vector [(1, 1), (1, 2), (1, 3), (1, 4)]
((1,2) + (1,3) + (1,4) + (1,5))

Properties:

prop> mapV id v == (v :: VectorSpace (Int, Int))

as well as @(mapV f (fmap g v)) == (map (f . g) v)@ and @(mapV f (v1 <> v2)) == ((mapV f v1) <> (mapV f v2))@.

/__TODO:__ add property-tests for the last two properties above. Difficulty: how to generate functions that are monotonically increasing with respect to the grading? Use suchThat function of QuickCheck./
-}
mapV :: (Scalar k, Basis a, Basis b) => (a -> b) -> VectorSpace k a -> VectorSpace k b
mapV f = vector . (map $ fmap f) . terms

{- | The same as @fmap@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(grading $ f b1) <= (grading $ f b2)@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 10 $ mapVG (*10) $ (basisVectorG [1..] :: VectorSpace Int Int)
((1,10) + (1,20) + (1,30) + (1,40) + (1,50) + (1,60) + (1,70) + (1,80) + (1,90) + (1,100))
-}
mapVG :: (Scalar k, Basis a, Basis b) => (a -> b) -> VectorSpace k a -> VectorSpace k b
mapVG f = vectorG . (map $ fmap f) . terms

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
linear f = vector . (concatMap applyf) . terms
  where
    applyf t = terms $ scaleV (scalar t) $ f $ basisElement t

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
    => (a -> VectorSpace k b)
    -> VectorSpace k a
    -> VectorSpace k b
linearG f = vectorG . (concatMap applyf) . terms
  where
    applyf t = terms $ scaleV (scalar t) $ f $ basisElement t

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
renormalize f = vectorG . (map renormalizeTerm) . terms
  where
    renormalizeTerm t = term (f (scalar t) (basisElement t)) $ basisElement t

scaleV :: (Scalar k, Basis a) => k -> VectorSpace k a -> VectorSpace k a
scaleV s = renormalize (\s0 x -> s * s0)

functional :: (Scalar k, Basis a) => (a -> k) -> VectorSpace k a -> k
functional f = sum . (map $ \t -> (scalar t) * (f $ basisElement t)) . terms

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
filterV :: (Scalar k, Basis a) => (Term k a -> Bool) -> VectorSpace k a -> VectorSpace k a
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

-- | A graded tensor algebra is defined as a graded vector space with the tensor product as the term. A tensor product is represented by a list of basis elements.
type TensorAlgebra k a = VectorSpace k [a]

{- | Tensor algebra is has an instance of the @Num@ class since both addition and multiplication are defined on it. To ensure that the product of two vectors in the tensor algebra is also in the tensor algebra, the product is distributed over the basis elements of the two vectors.

Examples:

>>> (vector [term 1 [1, 2], term 1 [3, 4]]) * (vector [term 1 [11, 12], term 1 [13, 14]])
(1 [1,2,11,12] + 1 [3,4,11,12] + 1 [1,2,13,14] + 1 [3,4,13,14])
-}
instance (Scalar k, Basis a) => Num (TensorAlgebra k a) where
    (+) = (<>)

    v1 * v2 =
        Vector $
            map (map mconcatProductMonoid) $
                distributeGradedLists $
                    map unVector $
                        [v1, v2]
      where
        productMonoidScalars t = (M.Product $ scalar t, basisElement t)
        unProductMonoidScalars t = term (M.getProduct $ fst t) (snd t)
        mconcatProductMonoid = unProductMonoidScalars . mconcat . (map productMonoidScalars)

    -- \| Absolute value of a vector makes no sense.
    abs = id

    -- \| Signum of a vector makes no sense either.
    signum _ = 1

    -- \| Inject integers into the tensor algebra.
    fromInteger i = vector [term (fromInteger i) []]

    negate = invert

{- | Take a function @f@ that maps basis elements to basis elements and extends it to a morphism of the tensor algebra.

Examples:

>>> morphismTP (\b -> b + 1) $ vector [basisTensorProduct [1, 2, 3, 4], basisTensorProduct [11, 12, 13, 14] :: TensorProduct (Int, Int)] :: TensorAlgebra (Int, Int)
(1 2 * 3 * 4 * 5 + 1 12 * 13 * 14 * 15)
-}
morphism
    :: ( Scalar k
       , Basis a
       , Basis b
       )
    => (a -> VectorSpace k b)
    -> TensorAlgebra k a
    -> TensorAlgebra k b
morphism f = linear $ product . (map $ (mapVG (: [])) . f)



-- TODO: define a product class with projections from and injections to the tensor algebra? This way the num and morphisms can be defined through those.
