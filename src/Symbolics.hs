{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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
    Term (..),
    basisTerm,
    scale,
    term,

    -- * Graded vector space

    --    VectorSpace,
    vector,
    vectorG,
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
    morphism,
    tensorCoproduct,
    Sum (Zero),
    fromListS,
    toListS,
    pattern (:+),
    PowerSeries (..),
    fromListPS,
    toListPS,

    -- * Debug
    (+:),
) where

import qualified Data.Bifunctor as BF (
    bimap,
 )
import Data.Group
import qualified Data.List as L (
    sortBy,
 )
import GradedList (
    Graded,
    distributeGradedLists,
    distributeLists,
    grading,
    groupByGrading,
    nDecList,
 )

{- $setup
>>> :set -XPatternSynonyms
>>> import Test.QuickCheck (Arbitrary (arbitrary), Gen)
>>> import Test.QuickCheck.Function (Fun (Fun), apply, pattern Fn)
>>> :{
instance Arbitrary (Term Integer Integer) where
   arbitrary = term <$> (arbitrary :: Gen Integer) <*> (arbitrary :: Gen [Integer])
:}

>>> :{
instance Arbitrary (Sum Integer Integer) where
   arbitrary = fromListS <$> (arbitrary :: Gen [Term Integer Integer])
:}

>>> :{
instance Arbitrary (PowerSeries Integer Integer) where
   arbitrary = vector <$> (arbitrary :: Gen (Sum Integer Integer))
:}
-}

-----------------------------------------------------------------------------

-- * Graded vector space

-----------------------------------------------------------------------------

--------------- Term ----------------

-- | A term is defined to be a pair of a scalar (@Num@) and a product of basis elements.
data Term k a = Term
    { scalar :: k
    , basisElement :: [a]
    }
    deriving (Eq)

instance (Show k, Show a) => Show (Term k a) where
    show (Term s b) = show s ++ " *^ " ++ show b

-- | Take a functions and extend it to a morphism.
instance Functor (Term k) where
    fmap f (Term s b) = Term s (map f b)

-- | Choose the product semigroup for the scalar type.
instance (Num k) => Semigroup (Term k a) where
    (Term s1 b1) <> (Term s2 b2) = Term (s1 * s2) (b1 <> b2)

instance (Num k) => Monoid (Term k a) where
    mempty = Term 1 mempty

term :: k -> [a] -> Term k a
term = Term

scale :: (Num k) => k -> Term k a -> Term k a
scale c1 t = term (c1 * scalar t) $ basisElement t

basisTerm :: (Num k) => [a] -> Term k a
basisTerm = term 1

instance (Graded a) => Graded (Term k a) where
    grading = grading . basisElement

--------------- Sum ----------------

pattern (:+) :: Term k a -> Sum k a -> Sum k a
pattern t :+ s <- Sum _ t s

{-# COMPLETE (:+), Zero #-}

-- | A sum is assumed to have a finite number of terms and a grading associated to it.
data Sum k a = Sum Integer (Term k a) (Sum k a) | Zero

{- | Construct a sum from a list of terms with the same grading. The list must be finite.

Examples:

>>> fromListS [term 1 [1], term 1 [2], term 1 [1], term 1 [2]]
2 *^ [1] + 2 *^ [2]
>>> fromListS [term 1 [1], term 1 [2], term 1 [1], term (-1) [2], term 1 [3]]
2 *^ [1] + 1 *^ [3]
-}
fromListS :: (Num k, Eq k, Graded a, Eq a) => [Term k a] -> Sum k a
fromListS l = case l of
    [] -> Zero
    (h : t) -> h +: fromListS t

toListS :: Sum k a -> [Term k a]
toListS Zero = []
toListS (h :+ s) = h : toListS s

lengthS :: Sum k a -> Int
lengthS = length . toListS

instance Graded (Sum k a) where
    grading Zero = 0
    grading (Sum g _ _) = g

instance (Show k, Show a) => Show (Sum k a) where
    show (t :+ Zero) = show t
    show (t :+ s) = show t ++ " + " ++ show s
    show Zero = "0"

infixr 7 +:

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> (term 1 [1]) +: (term 1 [1]) +: (term 1 [2]) +: Zero
2 *^ [1] + 1 *^ [2]
>>> (term 1 [3]) +: (term 1 [1]) +: (term 1 [2]) +: Zero
1 *^ [3] + 1 *^ [1] + 1 *^ [2]

Properties:

> (lengthS $ t +: l) - 1 <= lengthS (l :: Sum Integer Integer)
-}
(+:)
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => Term k a
    -> Sum k a
    -> Sum k a
(+:) (Term 0 _) s = s
(+:) t Zero = Sum (grading t) t Zero
(+:) t s@(Sum g _ _)
    | grading t /= g = error "Grading mismatch between a term and a sum"
    | otherwise = case maybeAddTerm t s of
        Nothing -> Sum g t s
        Just s' -> s'
  where
    maybeAddTerm _ Zero = Nothing
    maybeAddTerm t1 (t2 :+ s2) =
        if t1_basis == basisElement t2
            then
                if scalar_sum /= 0
                    then Just $ Sum g (term scalar_sum t1_basis) s2
                    else Just s2
            else case maybeAddTerm t1 s2 of
                Nothing -> Nothing
                Just s2' -> Just $ Sum g t2 s2'
      where
        t1_basis = basisElement t1
        scalar_sum = scalar t1 + scalar t2

{- | The semigroup structure of the sum is the addition of terms.

Examples:

>>> (term 1 [1]) +: (term 1 [2]) +: Zero <> ((term 1 [1]) +: (term (-1) [2]) +: (term 1 [3]) +: Zero)
2 *^ [1] + 1 *^ [3]

Properties:

> s1 <> s2 == s2 <> (s1 :: Sum Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Num k, Eq k, Eq a, Graded a) => Monoid (Sum k a) where
    mempty = Zero

{- | The inverse of a sum is the sum of the inverses of the terms.

Examples:

>>> invert $ (term 1 [1]) +: (term 1 [2]) +: Zero
-1 *^ [1] + -1 *^ [2]

Properties:

> invert s <> s == (mempty :: Sum Integer Integer)
> s <> invert s == (mempty :: Sum Integer Integer)
> invert (invert s) == (s :: Sum Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = term (negate $ scalar t) (basisElement t) +: invert s

{- | Two sums are equal if their difference is zero.

Examples:

>>> (term 1 [1]) +: (term 1 [2]) +: Zero == (term 1 [2]) +: (term 1 [1]) +: Zero
True

Properties:

> (s1 == s2) == (s1 - s2 == (mempty :: Sum Integer Integer))
-}
instance (Num k, Eq k, Eq a, Graded a) => Eq (Sum k a) where
    Zero == Zero = True
    (_ :+ _) == Zero = False
    Zero == (_ :+ _) = False
    s1 == s2 = (s1 <> invert s2) == Zero

{- | Both sum and product are well-defined over @Sum k a@. We use distributive property to define the product.

Examples:

>>> ((term 1 [1]) +: (term 1 [2]) +: Zero) * ((term 1 [1]) +: (term 1 [2]) +: Zero)
1 *^ [1,1] + 1 *^ [2,1] + 1 *^ [1,2] + 1 *^ [2,2]

Properties:

> s1 * (s2 * s3) == (s1 * s2) * (s3 :: Sum Integer Integer)
> s1 * (s2 + s3) == (s1 * s2) + (s1 * s3 :: Sum Integer Integer)
> (s1 + s2) * s3 == (s1 * s3) + (s2 * s3 :: Sum Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Num (Sum k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = term (fromInteger n) [] +: Zero

    abs = error "abs not implemented for Algebra"

    signum = error "signum not implemented for Algebra"

--------------- PowerSeries ----------------

infixr 6 :&

-- | A power series can have infinite number of terms.
data PowerSeries k a = (Sum k a) :& (PowerSeries k a) | Empty

fromListPS :: [Sum k a] -> PowerSeries k a
fromListPS = foldr (:&) Empty

toListPS :: PowerSeries k a -> [Sum k a]
toListPS Empty = []
toListPS (h :& ps) = h : toListPS ps

instance (Num k, Eq k, Eq a, Graded a) => Eq (PowerSeries k a) where
    Empty == Empty = True
    Empty == (Zero :& ps) = Empty == ps
    (Zero :& ps) == Empty = ps == Empty
    (s1 :& ps1) == (s2 :& ps2) = (s1 == s2) && (ps1 == ps2)
    _ == _ = False

instance (Show k, Show a) => Show (PowerSeries k a) where
    show = show_ 0
      where
        show_ :: (Show k, Show a) => Integer -> PowerSeries k a -> String
        show_ n Empty = "_" ++ show n
        show_ n (h :& Empty) = "(" ++ show h ++ ")_" ++ show n
        show_ n (Zero :& ps') = show_ (n + 1) ps'
        show_ n (h :& ps') = "(" ++ show h ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) ps'

{- | PowerSeries is a semigroup with addition as the operation.

Examples:

>>> (vector $ (term 1 [1]) +: (term 1 [2]) +: Zero) <> (vector $ (term 1 [1]) +: (term 1 [2]) +: (term 2 [3]) +: Zero)
(2 *^ [1] + 2 *^ [2] + 2 *^ [3])_1

Properties:

> v1 <> v2 == (v2 <> v1 :: PowerSeries Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (PowerSeries k a) where
    Empty <> ps = ps
    ps <> Empty = ps
    (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) :& (ps1 <> ps2)

{- | PowerSeries is a monoid with addition as the operation and the empty vector as the identity.

Examples:

>>> mempty :: PowerSeries Integer Integer
_0
>>> (vector $ (term 1 [1]) +: (term 1 [2]) +: Zero) <> mempty
(1 *^ [1] + 1 *^ [2])_1

Properties:

> v <> mempty == (v :: PowerSeries Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Monoid (PowerSeries k a) where
    mempty = Empty

{- | PowerSeries is a group with addition as the operation and negation as the inverse.

Examples:

>>> invert $ vector $ (term 1 [1]) +: (term 1 [2]) +: Zero
(-1 *^ [1] + -1 *^ [2])_1
>>> (vector $ (term 1 [1]) +: (term 1 [2]) +: Zero) <> invert (vector $ (term 1 [1]) +: (term 1 [2]) +: Zero)
(0)_1

Properties:

> v <> invert v == (mempty :: PowerSeries Integer Integer)
> invert v <> v == (mempty :: PowerSeries Integer Integer)
> invert (invert v) == (v :: PowerSeries Integer Integer)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (PowerSeries k a) where
    invert Empty = Empty
    invert (h :& ps) = invert h :& invert ps

{- | To ensure that the product of two power series is also a power series, the product is distributed over the basis elements of the two power series.

Examples:

>>> (vector $ (term 1 [1, 2]) +: (term 1 [3, 4]) +: Zero) * (vector $ (term 1 [11, 12]) +: (term 1 [13, 14]) +: Zero)
(1 *^ [1,2,11,12] + 1 *^ [3,4,11,12] + 1 *^ [1,2,13,14] + 1 *^ [3,4,13,14])_6
-}
instance (Num k, Eq k, Eq a, Graded a) => Num (PowerSeries k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListPS $ map (sum . map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListPS a, toListPS b]

    fromInteger n = fromInteger n :& Empty

    abs = error "abs not implemented for GradedAlgebra"

    signum = error "signum not implemented for GradedAlgebra"

--------------- PowerSeries Functions ----------------

{- | A flat list of terms.
Examples:

>>> terms $ Zero :& (term 1 [1] +: term 1 [2] +: Zero) :& Empty
[1 *^ [1],1 *^ [2]]
-}
terms :: PowerSeries k a -> [Term k a]
terms = concatMap toListS . toListPS

-- | A class of types that can be cast to a vector, i.e. PowerSeries k a.
class Vector v where
    type VectorScalar v
    type VectorBasis v
    vector :: v -> PowerSeries (VectorScalar v) (VectorBasis v)

{- | A product is cast to a vector with integer scalars. The implementation relies on the @Vector@ instance of @Term k a@.

Examples:

>>> vector [1,2,3]
(1 *^ [1,2,3])_3
-}
instance (Eq a, Graded a) => Vector [a] where
    type VectorScalar [a] = Integer
    type VectorBasis [a] = a
    vector = vector . term 1

{- | A term is cast to a vector with the same scalar and basis element. The implementation relies on the @Vector@ instance of @Sum k a@.

Examples:

>>> vector $ term 1 [1]
(1 *^ [1])_1
-}
instance (Num k, Eq k, Eq a, Graded a) => Vector (Term k a) where
    type VectorScalar (Term k a) = k
    type VectorBasis (Term k a) = a
    vector = vector . (+: Zero)

{- | Construct a vector from a sum.

Examples:

>>> vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [1]) +: (term 1 [2]) +: Zero
(2 *^ [1] + 2 *^ [2])_1
>>> vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [1]) +: (term (-1) [2]) +: (term 1 [3]) +: Zero
(2 *^ [1] + 1 *^ [3])_1
-}
instance (Num k, Eq k, Eq a, Graded a) => Vector (Sum k a) where
    type VectorScalar (Sum k a) = k
    type VectorBasis (Sum k a) = a
    vector = vectorG . L.sortBy compareGrading . toListS
      where
        compareGrading x y = compare (grading x) (grading y)

-- | @PowerSeries@ has a trivial @Vector@ instance.
instance Vector (PowerSeries k a) where
    type VectorScalar (PowerSeries k a) = k
    type VectorBasis (PowerSeries k a) = a
    vector = id

{- |  Construct a vector from a list of terms. The grading of terms in the list must be non-descreasing with finite number of terms having the same grading. The list itself may be infinite.

Examples:

>>> vectorG [term 1 [1], term 1 [2], term 1 [1], term 1 [2]]
(2 *^ [1] + 2 *^ [2])_1
>>> takeV 10 $ vectorG [term 1 [i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5] + 1 *^ [6] + 1 *^ [7] + 1 *^ [8] + 1 *^ [9])_1 + (1 *^ [10])_2
-}
vectorG
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [Term k a]
    -> PowerSeries k a
vectorG = fromListPS . map fromListS . groupByGrading . nDecList

-- | The same as @vectorG@ but with basis elements instead of terms.
basisVectorG
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [[a]]
    -> PowerSeries k a
basisVectorG = vectorG . map basisTerm

{- | Takes a function from the basis to a vector space and extends it to a linear map. The resulting function accepts only finite vectors.

!!! The function @f@ must preserve the grading.

Examples:

>>> linear (\[b]-> [b + 1]) $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
(1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5])_1
>>> linear (\[b] -> vector $ (term 1 [b]) +: (term 1 [b + 1]) +: Zero) $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
(1 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4] + 1 *^ [5])_1
-}
linear
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , Vector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => ([a] -> v)
    -> PowerSeries k a
    -> PowerSeries k b
linear f = sum . map (sum . map applyf . toListS) . toListPS
  where
    applyf t = scaleV (scalar t) $ vector $ f $ basisElement t

{- | The same as @linear@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(min $ grading $ f b1) <= (min $ grading $ f b2)@,

where @min@ is the minimum of the grading of the terms in the image of @f@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 9 $ linearG (\[b] -> basisVectorG [[i] | i <- [b..]]) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 2 *^ [2] + 3 *^ [3] + 4 *^ [4] + 5 *^ [5] + 6 *^ [6] + 7 *^ [7] + 8 *^ [8] + 9 *^ [9])_1
-}
linearG
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , Vector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => ([a] -> v)
    -> PowerSeries k a
    -> PowerSeries k b
linearG f = fromListPS . addLevels . map (toListPS . sum . map applyf . toListS) . toListPS
  where
    applyf t = scaleV (scalar t) $ vector $ f $ basisElement t
    addLevels = map sum . transposeUntilZero 0
    transposeUntilZero :: (Num k, Eq k, Eq b, Graded b) => Integer -> [[Sum k b]] -> [[Sum k b]]
    transposeUntilZero _ [] = []
    transposeUntilZero bound l =
        ( \(h, t) ->
            filter (/= Zero) (map snd h) : transposeUntilZero (newBound h) t
        )
            $ BF.bimap
                (takeWhile (\(i, x) -> x /= Zero || i <= bound) . zip [0 ..])
                (filter (/= []))
            $ unzip
            $ map splitList l
      where
        newBound [] = bound
        newBound [(i, _)] = i
        newBound (_ : t) = newBound t
        splitList (h : t) = (h, t)
        splitList [] = (Zero, [])

{- | Take a function @f@ that maps basis elements to basis elements and extends it to a morphism of the tensor algebra.

Examples:

>>> morphism (\b -> [b + 1]) $ vector $ (term 1 [1, 2, 3, 4]) +: (term 1 [5, 6, 7, 8]) +: Zero
(1 *^ [2,3,4,5] + 1 *^ [6,7,8,9])_4
-}
morphism
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , Vector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> PowerSeries k a
    -> PowerSeries k b
morphism f = linear $ product . map (vector . f)

{- | Change the coefficients in a vector using a function @f@ that takes the scalar and the basis element of a term and returns a new scalar.

Examples:

>>> renormalize (\s b -> s + 1) $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
(2 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4])_1
-}
renormalize
    :: ( Num k2
       , Eq k2
       , Eq a
       , Graded a
       )
    => (k1 -> [a] -> k2)
    -> PowerSeries k1 a
    -> PowerSeries k2 a
renormalize f = vectorG . map renormalizeTerm . terms
  where
    renormalizeTerm t = term (f (scalar t) (basisElement t)) $ basisElement t

{- | Scale a vector by a scalar.

Examples:

>>> scaleV 2 $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
(2 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4])_1
-}
scaleV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => k
    -> PowerSeries k a
    -> PowerSeries k a
scaleV s = renormalize (\s0 _ -> s * s0)

{- | Extends a function @f@ that maps basis elements to scalars to a linear functional. The resulting function accepts only finite vectors.

Examples:

>>> functional (\b -> fromInteger $ grading b) $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
4
-}
functional
    :: ( Num k
       , Eq k
       , Eq a
       )
    => ([a] -> k)
    -> PowerSeries k a
    -> k
functional f = sum . map (\t -> scalar t * f (basisElement t)) . terms

{- | The length of a vector is the number of terms in it.

Examples:

>>> lengthV $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
4

Properties:

> lengthV v == length (terms v :: [Term Integer Integer])
-}
lengthV :: PowerSeries k a -> Int
lengthV = sum . map lengthS . toListPS

{- | Take terms from a vector until the first term that does not satisfy the condition given by @f@.

Examples:

>>> takeWhileV (\(Term i [j]) -> j < 3) $ vector $ (term 1 [1]) +: (term 1 [2]) +: (term 1 [3]) +: (term 1 [4]) +: Zero
(1 *^ [1] + 1 *^ [2])_1
>>> takeWhileV (\(Term i [j]) -> j < 5) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4])_1

Properties:

> takeWhileV (\_ -> True) v == (v :: PowerSeries Integer Integer)
> takeWhileV (\_ -> False) v == (mempty :: PowerSeries Integer Integer)
-}
takeWhileV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (Term k a -> Bool)
    -> PowerSeries k a
    -> PowerSeries k a
takeWhileV f = vectorG . takeWhile f . terms

{- | Filter terms from a vector that satisfy the condition given by @f@.

Examples:

>>> takeV 10 $ filterV (\(Term _ [j]) -> j `mod` 3 == 0) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [3] + 1 *^ [6] + 1 *^ [9])_1 + (1 *^ [12] + 1 *^ [15] + 1 *^ [18] + 1 *^ [21] + 1 *^ [24] + 1 *^ [27] + 1 *^ [30])_2

Properties:

> filterV (\_ -> True) v == (v :: PowerSeries Integer Integer)
> filterV (\_ -> False) v == (mempty :: PowerSeries Integer Integer)
-}
filterV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (Term k a -> Bool)
    -> PowerSeries k a
    -> PowerSeries k a
filterV f = fromListPS . map (fromListS . filter f . toListS) . toListPS

{- | Take the first @n@ terms from a vector.

Examples:

>>> takeV 10 $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5] + 1 *^ [6] + 1 *^ [7] + 1 *^ [8] + 1 *^ [9])_1 + (1 *^ [10])_2

Properties:

> takeV (lengthV v) v == (v :: PowerSeries Integer Integer)
prop> takeV 0 v == (mempty :: PowerSeries Integer Integer)
-}
takeV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => Int
    -> PowerSeries k a
    -> PowerSeries k a
takeV n = vectorG . take n . terms

{- | Takes a product of basis elements and returns a tensor product of the corresponding basis vectors.

Examples:

>>> tensorCoproduct [1,2,3]
(1 *^ [[1,2,3],[]] + 1 *^ [[1,2],[3]] + 1 *^ [[1,3],[2]] + 1 *^ [[1],[2,3]] + 1 *^ [[2,3],[1]] + 1 *^ [[2],[1,3]] + 1 *^ [[3],[1,2]] + 1 *^ [[],[1,2,3]])_3
-}
tensorCoproduct
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [a]
    -> PowerSeries k [a]
-- tensorCoproduct = product . (map (\b -> basisVector [([b],[]), ([],[b])]))
tensorCoproduct = vector . fromListS . map basisTerm . listCoproduct
  where
    listCoproduct [] = [[[], []]] -- sum of tensor products of products
    listCoproduct (b : bs) =
        map
            (zipWith (<>) [[b], []])
            tailCoproduct
            ++ map
                (zipWith (<>) [[], [b]])
                tailCoproduct
      where
        tailCoproduct = listCoproduct bs

-- TODO: define a product class with projections from and injections to the tensor algebra? This way the num and morphisms can be defined through those.
