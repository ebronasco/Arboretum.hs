{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : Symbolics
Description : Symbolic algebra in Haskell using graded vector spaces.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

An implementation of symbolic algebra using graded vector spaces
with the aim of being able to represent and manipulate algebras over
the vector spaces of graphs.
-}
module Symbolics (
    ScalarProduct,
    pattern (:*^),
    (*^),
    scale,

    -- * Graded vector space

    --    VectorSpace,
    Vector (..),
    vector,
    fromListV,
    fromInfListV,
    terms,
    basisElements,
    linear,
    linearG,
    renormalize,
    scaleV,
    functional,
    lengthV,
    takeWhileV,
    filterV,
    takeV,
    morphism,
    Sum (Zero),
    fromListS,
    toListS,
    pattern (:+),
    (+:),
    PowerSeries (..),
    fromListPS,
    toListPS,
    tensorCoproduct,
    bilinear,
) where

import qualified Data.Bifunctor as BF (
    bimap,
 )
import Data.Group
import qualified Data.List as L (
    sortBy,
 )
import qualified Data.MultiSet as MS (
    MultiSet,
    fromList,
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
instance (Num k, Arbitrary k, Arbitrary a) => Arbitrary (ScalarProduct k a) where
   arbitrary = (*^) <$> (arbitrary :: Gen k) <*> (arbitrary :: Gen a)
:}

>>> :{
instance (Num k, Eq k, Eq a, Graded a, Arbitrary k, Arbitrary a) => Arbitrary (Sum k a) where
   arbitrary = fromListS <$> (arbitrary :: Gen [ScalarProduct k a])
:}

>>> :{
instance (Num k, Eq k, Eq a, Graded a, Arbitrary k, Arbitrary a) => Arbitrary (PowerSeries k a) where
   arbitrary = vector <$> (arbitrary :: Gen (Sum k a))
:}
-}

-----------------------------------------------------------------------------

-- * Graded vector space

-----------------------------------------------------------------------------

--------------- Scalar product ----------------

pattern (:*^) :: k -> a -> ScalarProduct k a
pattern k :*^ a <- ScalarProduct k a

{-# COMPLETE (:*^) #-}

-- | A scalar product is defined to be a pair of a scalar (@Num@) and a basis element.
data ScalarProduct k a = ScalarProduct
    { scalar :: k
    , basisElement :: a
    }
    deriving (Eq)

instance (Show k, Show a) => Show (ScalarProduct k a) where
    show (s :*^ b) = show s ++ " *^ " ++ show b

-- | Take a functions and extend it linearly
instance (Num k) => Functor (ScalarProduct k) where
    fmap f (s :*^ b) = s *^ f b

-- | Choose the product semigroup for the scalar type.
instance (Num k, Semigroup a) => Semigroup (ScalarProduct k a) where
    (s1 :*^ b1) <> (s2 :*^ b2) = (s1 * s2) *^ (b1 <> b2)

instance (Num k, Monoid a) => Monoid (ScalarProduct k a) where
    mempty = 1 *^ mempty

infix 7 *^

(*^) :: (Num k) => k -> a -> ScalarProduct k a
(*^) = ScalarProduct

scale :: (Num k) => k -> ScalarProduct k a -> ScalarProduct k a
scale s1 (s2 :*^ a) = (s1 * s2) *^ a

instance (Graded a) => Graded (ScalarProduct k a) where
    grading = grading . basisElement

--------------- Sum ----------------

pattern (:+) :: ScalarProduct k a -> Sum k a -> Sum k a
pattern t :+ s <- Sum _ t s

{-# COMPLETE (:+), Zero #-}

-- | A sum is assumed to have a finite number of terms and a grading associated to it.
data Sum k a = Sum Integer (ScalarProduct k a) (Sum k a) | Zero

{- | Construct a sum from a list of terms with the same grading. The list must be finite.

Examples:

>>> fromListS [1 *^ 'x', 1 *^ 'y', 1 *^ 'x', 1 *^ 'y']
2 *^ 'x' + 2 *^ 'y'
>>> fromListS [1 *^ 'x', 1 *^ 'y', 1 *^ 'x', (-1) *^ 'y', 1 *^ 'z']
2 *^ 'x' + 1 *^ 'z'
-}
fromListS :: (Num k, Eq k, Graded a, Eq a) => [ScalarProduct k a] -> Sum k a
fromListS l = case l of
    [] -> Zero
    (h : t) -> h +: fromListS t

toListS :: Sum k a -> [ScalarProduct k a]
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

infixr 6 +:

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> (1 *^ 'x') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
2 *^ 'x' + 1 *^ 'y'
>>> (1 *^ 'z') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
1 *^ 'z' + 1 *^ 'x' + 1 *^ 'y'

Properties:

> (lengthS $ t +: l) - 1 <= lengthS (l :: Sum Integer Char)
-}
(+:)
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => ScalarProduct k a
    -> Sum k a
    -> Sum k a
(+:) (0 :*^ _) s = s
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
                    then Just $ Sum g (scalar_sum *^ t1_basis) s2
                    else Just s2
            else case maybeAddTerm t1 s2 of
                Nothing -> Nothing
                Just s2' -> Just $ Sum g t2 s2'
      where
        t1_basis = basisElement t1
        scalar_sum = scalar t1 + scalar t2

{- | The semigroup structure of the sum is the addition of terms.

Examples:

>>> (1 *^ 'x') +: (1 *^ 'y') +: Zero <> ((1 *^ 'x') +: ((-1) *^ 'y') +: (1 *^ 'z') +: Zero)
2 *^ 'x' + 1 *^ 'z'

Properties:

> s1 <> s2 == s2 <> (s1 :: Sum Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Num k, Eq k, Eq a, Graded a) => Monoid (Sum k a) where
    mempty = Zero

{- | The inverse of a sum is the sum of the inverses of the terms.

Examples:

>>> invert $ (1 *^ 'x') +: (1 *^ 'y') +: Zero
-1 *^ 'x' + -1 *^ 'y'

Properties:

> invert s <> s == (mempty :: Sum Integer Char)
> s <> invert s == (mempty :: Sum Integer Char)
> invert (invert s) == (s :: Sum Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = negate (scalar t) *^ basisElement t +: invert s

{- | Two sums are equal if their difference is zero.

Examples:

>>> (1 *^ 'x') +: (1 *^ 'y') +: Zero == (1 *^ 'y') +: (1 *^ 'x') +: Zero
True

Properties:

> (s1 == s2) == (s1 - s2 == (mempty :: Sum Integer Char))
-}
instance (Num k, Eq k, Eq a, Graded a) => Eq (Sum k a) where
    Zero == Zero = True
    (_ :+ _) == Zero = False
    Zero == (_ :+ _) = False
    s1 == s2 = (s1 <> invert s2) == Zero

{- | Both sum and product are well-defined over @Sum k a@. We use distributive property to define the product.

Examples:

>>> ((1 *^ "x") +: (1 *^ "y") +: Zero) * ((1 *^ "x") +: (1 *^ "y") +: Zero)
1 *^ "xx" + 1 *^ "yx" + 1 *^ "xy" + 1 *^ "yy"

Properties:

> s1 * (s2 * s3) == (s1 * s2) * (s3 :: Sum Integer Char)
> s1 * (s2 + s3) == (s1 * s2) + (s1 * s3 :: Sum Integer Char)
> (s1 + s2) * s3 == (s1 * s3) + (s2 * s3 :: Sum Integer Char)
-}
instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    , Monoid a
    )
    => Num (Sum k a)
    where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = fromInteger n *^ mempty +: Zero

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

instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    )
    => Eq (PowerSeries k a)
    where
    Empty == Empty = True
    Empty == (Zero :& ps) = Empty == ps
    (Zero :& ps) == Empty = ps == Empty
    (s1 :& ps1) == (s2 :& ps2) = (s1 == s2) && (ps1 == ps2)
    _ == _ = False

instance
    ( Show k
    , Show a
    )
    => Show (PowerSeries k a)
    where
    show = show_ 0
      where
        show_ :: (Show k, Show a) => Integer -> PowerSeries k a -> String
        show_ n Empty = "_" ++ show n
        show_ n (h :& Empty) = "(" ++ show h ++ ")_" ++ show n
        show_ n (Zero :& ps') = show_ (n + 1) ps'
        show_ n (h :& ps') = "(" ++ show h ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) ps'

{- | PowerSeries is a semigroup with addition as the operation.

Examples:

>>> (vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero) <> (vector $ (1 *^ 'x') +: (1 *^ 'y') +: (2 *^ 'z') +: Zero)
(2 *^ 'x' + 2 *^ 'y' + 2 *^ 'z')_1

Properties:

> v1 <> v2 == (v2 <> v1 :: PowerSeries Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (PowerSeries k a) where
    Empty <> ps = ps
    ps <> Empty = ps
    (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) :& (ps1 <> ps2)

{- | PowerSeries is a monoid with addition as the operation and the empty vector as the identity.

Examples:

>>> mempty :: PowerSeries Integer Char
_0
>>> (vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero) <> mempty
(1 *^ 'x' + 1 *^ 'y')_1

Properties:

> v <> mempty == (v :: PowerSeries Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Monoid (PowerSeries k a) where
    mempty = Empty

{- | PowerSeries is a group with addition as the operation and negation as the inverse.

Examples:

>>> invert $ vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero
(-1 *^ 'x' + -1 *^ 'y')_1
>>> (vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero) <> invert (vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero)
(0)_1

Properties:

> v <> invert v == (mempty :: PowerSeries Integer Char)
> invert v <> v == (mempty :: PowerSeries Integer Char)
> invert (invert v) == (v :: PowerSeries Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (PowerSeries k a) where
    invert Empty = Empty
    invert (h :& ps) = invert h :& invert ps

{- | To ensure that the product of two power series is also a power series, the product is distributed over the basis elements of the two power series.

Examples:

>>> (vector $ (1 *^ "xy") +: (1 *^ "zw") +: Zero) * (vector $ (1 *^ "xxyy") +: (1 *^ "zzww") +: Zero)
(1 *^ "xyxxyy" + 1 *^ "zwxxyy" + 1 *^ "xyzzww" + 1 *^ "zwzzww")_6
-}
instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    , Monoid a
    )
    => Num (PowerSeries k a)
    where
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

>>> terms $ Zero :& (1 *^ 'x' +: 1 *^ 'y' +: Zero) :& Empty
[1 *^ 'x',1 *^ 'y']
-}
terms :: PowerSeries k a -> [ScalarProduct k a]
terms = concatMap toListS . toListPS

{- | A list of basis elements of a power series.

Examples:

>>> basisElements $ vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
"xy"
-}
basisElements :: PowerSeries k a -> [a]
basisElements = map basisElement . terms

-- | A class of types that can be cast to a vector, i.e. PowerSeries k a.
class Vector v where
    type VectorScalar v
    type VectorBasis v
    vector :: v -> PowerSeries (VectorScalar v) (VectorBasis v)

{- | A MultiSet is often used to represent a commutative product and as a basis of an algebra.

Examples:

>>> vector $ MS.fromList "xy"
(1 *^ "xy")_2
-}
instance (Eq a, Graded a) => Vector (MS.MultiSet a) where
    type VectorScalar (MS.MultiSet a) = Integer
    type VectorBasis (MS.MultiSet a) = MS.MultiSet a
    vector = vector . (1 *^)

{- | A list is often used to represent a product and as a basis of an algebra.

Examples:

>>> vector "xy"
(1 *^ "xy")_2
-}
instance (Eq a, Graded a) => Vector [a] where
    type VectorScalar [a] = Integer
    type VectorBasis [a] = [a]
    vector = vector . (1 *^)

{- | A term is cast to a vector with the same scalar and basis element. The implementation relies on the @Vector@ instance of @Sum k a@.

Examples:

>>> vector $ 1 *^ 'x'
(1 *^ 'x')_1
-}
instance (Num k, Eq k, Eq a, Graded a) => Vector (ScalarProduct k a) where
    type VectorScalar (ScalarProduct k a) = k
    type VectorBasis (ScalarProduct k a) = a
    vector = vector . (+: Zero)

{- | Construct a vector from a sum.

Examples:

>>> vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
(2 *^ 'x' + 2 *^ 'y')_1
>>> vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: ((-1) *^ 'y') +: (1 *^ 'z') +: Zero
(2 *^ 'x' + 1 *^ 'z')_1
-}
instance (Num k, Eq k, Eq a, Graded a) => Vector (Sum k a) where
    type VectorScalar (Sum k a) = k
    type VectorBasis (Sum k a) = a
    vector Zero = Empty
    vector s@(Sum g _ _) = fromListPS $ replicate (fromInteger g) Zero ++ [s]

-- | @PowerSeries@ has a trivial @Vector@ instance.
instance Vector (PowerSeries k a) where
    type VectorScalar (PowerSeries k a) = k
    type VectorBasis (PowerSeries k a) = a
    vector = id

{- | Construct a vector from a finite list of terms.

Examples:

>>> fromListV [1 *^ "x", 1 *^ "y", 3 *^ "xy", 1 *^ "x", 1 *^ "y"]
(2 *^ "x" + 2 *^ "y")_1 + (3 *^ "xy")_2
-}
fromListV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [ScalarProduct k a]
    -> PowerSeries k a
fromListV = fromInfListV . L.sortBy compareGrading
  where
    compareGrading x y = compare (grading x) (grading y)

{- |  Construct a vector from a list of terms. The grading of terms in the list must be non-descreasing with finite number of terms having the same grading. The list itself may be infinite.

Examples:

>>> fromInfListV [1 *^ 'x', 1 *^ 'y', 1 *^ 'x', 1 *^ 'y']
(2 *^ 'x' + 2 *^ 'y')_1
>>> takeV 10 $ fromInfListV [1 *^ i | i <- [1..]]
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5 + 1 *^ 6 + 1 *^ 7 + 1 *^ 8 + 1 *^ 9)_1 + (1 *^ 10)_2
-}
fromInfListV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [ScalarProduct k a]
    -> PowerSeries k a
fromInfListV = fromListPS . map fromListS . groupByGrading . nDecList

{- | Takes a function from the basis to a vector space and extends it to a linear map. The resulting function accepts only finite vectors.

!!! The function @f@ must preserve the grading.

Examples:

 >>> linear (\b -> 1 *^ (b + 1)) $ vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
(1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5)_1
>>> linear (\b -> vector $ (1 *^ b) +: (1 *^ (b + 1)) +: Zero) $ vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
(1 *^ 1 + 2 *^ 2 + 2 *^ 3 + 2 *^ 4 + 1 *^ 5)_1
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
    => (a -> v)
    -> PowerSeries k a
    -> PowerSeries k b
linear f = mconcat . map (mconcat . map applyf . toListS) . toListPS
  where
    applyf t = scaleV (scalar t) $ vector $ f $ basisElement t

{- | The same as @linear@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(min $ grading $ f b1) <= (min $ grading $ f b2)@,

where @min@ is the minimum of the grading of the terms in the image of @f@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 9 $ linearG (\b -> fromInfListV [1 *^ i | i <- [b..]]) $ fromInfListV [1 *^ i | i <- [1..]]
(1 *^ 1 + 2 *^ 2 + 3 *^ 3 + 4 *^ 4 + 5 *^ 5 + 6 *^ 6 + 7 *^ 7 + 8 *^ 8 + 9 *^ 9)_1
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
    => (a -> v)
    -> PowerSeries k a
    -> PowerSeries k b
linearG f = fromListPS . addLevels . map (toListPS . mconcat . map applyf . toListS) . toListPS
  where
    applyf t = scaleV (scalar t) $ vector $ f $ basisElement t
    addLevels = map mconcat . transposeUntilZero 0
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

>>> morphism (\b -> [b + 1]) $ vector $ (1 *^ [1, 2, 3, 4]) +: (1 *^ [5, 6, 7, 8]) +: Zero
(1 *^ [2,3,4,5] + 1 *^ [6,7,8,9])_4
-}
morphism
    :: ( Num k
       , Eq k
       , Functor f
       , Foldable f
       , Eq (f a)
       , Eq b
       , Graded b
       , Monoid b
       , Vector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> PowerSeries k (f a)
    -> PowerSeries k b
morphism f = linearG $ product . fmap (vector . f)

{- | Change the coefficients in a vector using a function @f@ that takes the scalar and the basis element of a term and returns a new scalar.

Examples:

>>> renormalize (\s b -> s + 1) $ vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
(2 *^ 'x' + 3 *^ 'y' + 4 *^ 'z' + 5 *^ 'w')_1
-}
renormalize
    :: ( Num k2
       , Eq k2
       , Eq a
       , Graded a
       )
    => (k1 -> a -> k2)
    -> PowerSeries k1 a
    -> PowerSeries k2 a
renormalize f = fromInfListV . map renormalizeTerm . terms
  where
    renormalizeTerm t = f (scalar t) (basisElement t) *^ basisElement t

{- | Scale a vector by a scalar.

Examples:

>>> scaleV 2 $ vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
(2 *^ 'x' + 4 *^ 'y' + 6 *^ 'z' + 8 *^ 'w')_1
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

>>> functional (\b -> fromInteger $ grading b) $ vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
10
-}
functional
    :: ( Num k
       , Eq k
       , Eq a
       )
    => (a -> k)
    -> PowerSeries k a
    -> k
functional f = sum . map (\t -> scalar t * f (basisElement t)) . terms

{- | The length of a vector is the number of terms in it.

Examples:

>>> lengthV $ vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'z') +: (1 *^ 'w') +: Zero
4

Properties:

> lengthV v == length (terms v :: [ScalarProduct Integer Char])
-}
lengthV :: PowerSeries k a -> Int
lengthV = sum . map lengthS . toListPS

{- | Take terms from a vector until the first term that does not satisfy the condition given by @f@.

Examples:

>>> takeWhileV (\(i :*^ j) -> j < 3) $ vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
(1 *^ 1 + 1 *^ 2)_1
>>> takeWhileV (\(i :*^ j) -> j < 5) $ fromInfListV [1 *^ i | i <- [1..]]
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4)_1

Properties:

> takeWhileV (\_ -> True) v == (v :: PowerSeries Integer Char)
> takeWhileV (\_ -> False) v == (mempty :: PowerSeries Integer Char)
-}
takeWhileV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (ScalarProduct k a -> Bool)
    -> PowerSeries k a
    -> PowerSeries k a
takeWhileV f = fromInfListV . takeWhile f . terms

{- | Filter terms from a vector that satisfy the condition given by @f@.

Examples:

>>> takeV 10 $ filterV (\(_ :*^ j) -> j `mod` 3 == 0) $ fromInfListV [1 *^ i | i <- [1..]]
(1 *^ 3 + 1 *^ 6 + 1 *^ 9)_1 + (1 *^ 12 + 1 *^ 15 + 1 *^ 18 + 1 *^ 21 + 1 *^ 24 + 1 *^ 27 + 1 *^ 30)_2

Properties:

> filterV (\_ -> True) v == (v :: PowerSeries Integer Char)
> filterV (\_ -> False) v == (mempty :: PowerSeries Integer Char)
-}
filterV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (ScalarProduct k a -> Bool)
    -> PowerSeries k a
    -> PowerSeries k a
filterV f = fromListPS . map (fromListS . filter f . toListS) . toListPS

{- | Take the first @n@ terms from a vector.

Examples:

>>> takeV 10 $ fromInfListV [1 *^ i | i <- [1..]]
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5 + 1 *^ 6 + 1 *^ 7 + 1 *^ 8 + 1 *^ 9)_1 + (1 *^ 10)_2

Properties:

> takeV (lengthV v) v == (v :: PowerSeries Integer Char)
prop> takeV 0 v == (mempty :: PowerSeries Integer Char)
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
takeV n = fromInfListV . take n . terms

-----------------------------------------------------------------------------

-- * Tensor algebra

-----------------------------------------------------------------------------

instance (Eq a, Graded a, Eq b, Graded b) => Vector (a, b) where
    type VectorScalar (a, b) = Integer
    type VectorBasis (a, b) = (a, b)
    vector = vector . (1 *^)

instance (Graded a, Graded b) => Graded (a, b) where
    grading (a, b) = grading a + grading b

{- | Takes a product of basis elements and returns a tensor product of the corresponding basis vectors.

Examples:

>>> tensorCoproduct [1,2,3]
(1 *^ ([],[1,2,3]) + 1 *^ ([1],[2,3]) + 1 *^ ([3],[1,2]) + 1 *^ ([2],[1,3]) + 1 *^ ([1,3],[2]) + 1 *^ ([1,2],[3]) + 1 *^ ([2,3],[1]) + 1 *^ ([1,2,3],[]))_3
-}
tensorCoproduct
    :: ( Eq a
       , Graded a
       )
    => [a]
    -> PowerSeries Integer ([a], [a])
tensorCoproduct =
    product
        . map (\b -> vector ([], [b]) + vector ([b], []))

{- | Takes a function with two arguments and extends it to a bilinear map.

Examples:

>>> bilinear (\a b -> [a + b]) (vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero) (vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero)
(1 *^ [2] + 2 *^ [3] + 3 *^ [4] + 4 *^ [5] + 3 *^ [6] + 2 *^ [7] + 1 *^ [8])_1
-}
bilinear
    :: ( Vector v
       , Num k
       , Eq k
       , Eq a
       , Eq b
       , Eq c
       , Graded a
       , Graded b
       , Graded c
       , VectorScalar v ~ k
       , VectorBasis v ~ c
       )
    => (a -> b -> v)
    -> PowerSeries k a
    -> PowerSeries k b
    -> PowerSeries k c
bilinear f ps1 ps2 =
    linear (uncurry f . BF.bimap head head) $
        linear ((1 *^) . (,[]) . (: [])) ps1 * linear ((1 *^) . ([],) . (: [])) ps2
