{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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
    IsVector (..),
    vectorFromList,
    vectorFromNonDecList,
    terms,
    basisElements,
    linear,
    linearGraded,
    linearNonDec,
    renormalize,
    scaleV,
    rescale,
    functional,
    lengthV,
    takeWhileV,
    filterV,
    takeV,
    morphism,
    morphismGraded,
    morphismNonDec,
    Sum (Zero),
    fromListS,
    toListS,
    pattern (:+),
    (+:),
    Vector (Empty),
    fromListV,
    toListV,
    deshuffleCoproduct,
    bilinear,
    bilinearGraded,
    bilinearNonDec,
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
>>> :set -XPatternSynonyms -XTypeFamilies
>>> import Test.QuickCheck (Arbitrary (arbitrary), Gen)
>>> import Test.QuickCheck.Function (Fun (Fun), apply, pattern Fn)
>>> import qualified Data.MultiSet as MS (fromList)
>>> newtype Singleton a = Singleton [a] deriving (Show, Eq, Graded, Semigroup, Monoid)
>>> :{
instance Arbitrary a => Arbitrary (Singleton a) where
    arbitrary = Singleton <$> (:[]) <$> arbitrary
:}

>>> :{
instance (Arbitrary a, Ord a) => Arbitrary (MS.MultiSet a) where
    arbitrary = MS.fromList <$> arbitrary
:}

>>> :{
instance (Num k, Arbitrary k, Arbitrary a) => Arbitrary (ScalarProduct k a) where
   arbitrary = (*^) <$> (arbitrary :: Gen k) <*> (arbitrary :: Gen a)
:}

>>> :{
instance (Num k, Eq k, Eq a, Graded a, Arbitrary k, Arbitrary a) => Arbitrary (Sum k a) where
   arbitrary = fromListS <$> (arbitrary :: Gen [ScalarProduct k a])
:}

>>> :{
instance (Num k, Eq k, Eq a, Graded a, Arbitrary k, Arbitrary a) => Arbitrary (Vector k a) where
   arbitrary = vectorFromList <$> (arbitrary :: Gen [ScalarProduct k a])
:}

>>> :{
instance IsVector Char where
    type VectorScalar Char = Integer
    type VectorBasis Char = Char
    vector = vector . (1 *^)
:}
-}

-----------------------------------------------------------------------------

-- * Scalar Product

-----------------------------------------------------------------------------

pattern (:*^) :: k -> a -> ScalarProduct k a
pattern k :*^ a <- ScalarProduct k a

{-# COMPLETE (:*^) #-}

-- | A scalar product is defined to be a pair of a scalar (@Num@) and
-- a basis element.
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

----------------------------------------------------------------------

-- * Sum

----------------------------------------------------------------------

pattern (:+) :: ScalarProduct k a -> Sum k a -> Sum k a
pattern t :+ s <- Sum _ t s

{-# COMPLETE (:+), Zero #-}

-- | A sum is assumed to have a finite number of terms and a grading
-- associated to it.
data Sum k a = Sum Integer (ScalarProduct k a) (Sum k a) | Zero

{- |
  Construct a sum from a list of terms with the same grading.
  The list must be finite.

Examples:

>>> l = [1 *^ 'x', 1 *^ 'y', 1 *^ 'z', 1 *^ 'x', 1 *^ 'y', (-2) *^ 'z'] :: [ScalarProduct Integer Char]
>>> fromListS l
2 *^ 'x' + 2 *^ 'y' + -1 *^ 'z'

Properties:

prop> \l -> lengthS (fromListS l) <= length (l :: [ScalarProduct Integer Char])
-}
fromListS :: (Num k, Eq k, Graded a, Eq a) => [ScalarProduct k a] -> Sum k a
fromListS l = case l of
    [] -> Zero
    (h : t) -> h +: fromListS t

{- |
  Construct a list of terms from a sum.

Examples:

>>> s = 2 *^ 'x' +: 2 *^ 'y' +: Zero :: Sum Integer Char
>>> toListS s
[2 *^ 'x',2 *^ 'y']

Properties:

prop> \s -> length (toListS s) == lengthS (s :: Sum Integer Char)
-}
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

{- |
  Adds a term to a sum ensuring that every term in the sum has a
  unique basis element and the same grading.

Examples:

>>> (1 *^ 'x') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
2 *^ 'x' + 1 *^ 'y'
>>> (1 *^ 'z') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
1 *^ 'z' + 1 *^ 'x' + 1 *^ 'y'

Properties:

prop> \t l -> (lengthS $ t +: l) - 1 <= lengthS (l :: Sum Integer Char)
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

{- |
  The semigroup structure of the sum is the addition of terms.

Examples:

>>> s1 = (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> s2 = (1 *^ 'x') +: ((-1) *^ 'y') +: (1 *^ 'z') +: Zero
>>> s1  <> s2
2 *^ 'x' + 1 *^ 'z'

Properties:

prop> \s1 s2 -> s1 <> s2 == s2 <> (s1 :: Sum Integer Char)
prop> \s1 s2 s3 -> s1 <> (s2 <> s3) == (s1 <> s2) <> (s3 :: Sum Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

{- |
  A sum is a monoid with neutral element zero.

Properties:

prop> \s -> s <> mempty == (s :: Sum Integer Char)
prop> \s -> mempty <> s == (s :: Sum Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Monoid (Sum k a) where
    mempty = Zero

{- |
  The inverse of a sum is the sum of the inverses of the terms.

Examples:

>>> s = (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> invert s
-1 *^ 'x' + -1 *^ 'y'

Properties:

prop> \s -> invert s <> s == (mempty :: Sum Integer Char)
prop> \s -> s <> invert s == (mempty :: Sum Integer Char)
prop> \s -> invert (invert s) == (s :: Sum Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = negate (scalar t) *^ basisElement t +: invert s

{- |
  Two sums are equal if their difference is zero.

Examples:

>>> s1 = (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> s2 = (1 *^ 'y') +: (1 *^ 'x') +: Zero
>>> s1 == s2
True

Properties:

prop> \s1 s2 -> (s1 == s2) == ((invert s1) <> s2 == (mempty :: Sum Integer Char))
-}
instance (Num k, Eq k, Eq a, Graded a) => Eq (Sum k a) where
    Zero == Zero = True
    (_ :+ _) == Zero = False
    Zero == (_ :+ _) = False
    s1 == s2 = (s1 <> invert s2) == Zero

{- |
  If @a@ is a monoid, the operation of the monoid is taken to be the
  product which is extended to @Sum k a@ through distributivity.

Examples:

>>> s1 = (1 *^ "x") +: (1 *^ "y") +: Zero
>>> s2 = (2 *^ "x") +: (3 *^ "y") +: Zero
>>> s1 * s2
2 *^ "xx" + 2 *^ "yx" + 3 *^ "xy" + 3 *^ "yy"

Properties:

> \s1 s2 s3 -> s1 * (s2 * s3) == (s1 * s2) * (s3 :: Sum Integer (Singleton Char))
> \s1 s2 s3 -> s1 * (s2 + s3) == (s1 * s2) + (s1 * (s3 :: Sum Integer (Singleton Char)))
> \s1 s2 s3 -> (s1 + s2) * s3 == (s1 * s3) + (s2 * (s3 :: Sum Integer (Singleton Char)))
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

----------------------------------------------------------------------

-- * Vector

----------------------------------------------------------------------

pattern (:&) :: Sum k a -> Vector k a -> Vector k a
pattern t :& s <- Vector t s

{-# COMPLETE (:&), Empty #-}

-- | A power series can have infinite number of terms.
data Vector k a = Vector (Sum k a) (Vector k a) | Empty

{- |
  Construct a vector from a list of sums where position @i@ of the
  list is holds a sum with grading @i@ or @0@.  The list may be
  infinite.

Examples:

>>> s1 = (1 *^ "") +: Zero
>>> s2 = (1 *^ "x") +: (1 *^ "y") +: (2 *^ "z") +: Zero
>>> s3 = (1 *^ "xx") +: (1 *^ "xy") +: (2 *^ "zz") +: Zero
>>> fromListV [s1, s2, s3]
(1 *^ "")_0 + (1 *^ "x" + 1 *^ "y" + 2 *^ "z")_1 + (1 *^ "xx" + 1 *^ "xy" + 2 *^ "zz")_2

>>> fromListV [s2, s3]
*** Exception: Grading mismatch in a list of terms
...
>>> fromListV [s1, s3]
(1 *^ "")_0*** Exception: Grading mismatch in a list of terms
...
>>> fromListV [s1, Zero, s3, Zero]
(1 *^ "")_0 + (1 *^ "xx" + 1 *^ "xy" + 2 *^ "zz")_2
-}
fromListV :: (Num k, Eq k, Eq a, Graded a) => [Sum k a] -> Vector k a
fromListV = foldr (&:) Empty . checkGrading 0
  where
    checkGrading _ [] = []
    checkGrading n (x : xs)
        | x == Zero = x : checkGrading (n + 1) xs
        | grading x == n = x : checkGrading (n + 1) xs
        | otherwise = error "Grading mismatch in a list of terms"

{- |
  Return a list of sums from a vector.

Examples:

>>> v = Zero &: (1 *^ "x") +: (1 *^ "y") +: Zero &: (1 *^ "xy") +: (1 *^ "yx") +: (2 *^ "zz") +: Zero &: Empty
>>> toListV v
[0,1 *^ "x" + 1 *^ "y",1 *^ "xy" + 1 *^ "yx" + 2 *^ "zz"]
-}
toListV :: Vector k a -> [Sum k a]
toListV Empty = []
toListV (h :& ps) = h : toListV ps

infixr 5 &:

(&:) :: Sum k a -> Vector k a -> Vector k a
(&:) = Vector

-- | Two vectors are equal if each pair of sums with equal grading
-- are equal.
instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    )
    => Eq (Vector k a)
    where
    Empty == Empty = True
    Empty == (Zero :& ps) = Empty == ps
    (Zero :& ps) == Empty = ps == Empty
    (s1 :& ps1) == (s2 :& ps2) = (s1 == s2) && (ps1 == ps2)
    _ == _ = False

-- | Display the vector as a string
instance
    ( Show k
    , Show a
    , Num k
    , Eq k
    , Eq a
    , Graded a
    )
    => Show (Vector k a)
    where
    show v
        | v == Empty = "_0"
        | otherwise = show_ 0 "" v
      where
        show_ :: (Show k, Show a) => Integer -> String -> Vector k a -> String
        show_ _ _ Empty = ""
        show_ n delim (Zero :& ps') = show_ (n + 1) delim ps'
        show_ n delim (h :& ps') = delim ++ "(" ++ show h ++ ")_" ++ show n ++ show_ (n + 1) " + " ps'

{- |
  Vector is a semigroup with addition as the operation.

Examples:

>>> v1 = vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> v2 = vector $ (1 *^ 'x') +: (1 *^ 'y') +: (2 *^ 'z') +: Zero
>>> v1 <> v2
(2 *^ 'x' + 2 *^ 'y' + 2 *^ 'z')_1

Properties:

prop> \v1 v2 -> v1 <> v2 == (v2 <> v1 :: Vector Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Semigroup (Vector k a) where
    Empty <> ps = ps
    ps <> Empty = ps
    (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) &: (ps1 <> ps2)

{- |
  Vector is a monoid with addition as the operation and the empty
  vector as the identity.

Examples:

>>> mempty :: Vector Integer Char
_0
>>> v = vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> v <> mempty
(1 *^ 'x' + 1 *^ 'y')_1

Properties:

prop> \v -> v <> mempty == (v :: Vector Integer Char)
prop> \v -> mempty <> v == (v :: Vector Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Monoid (Vector k a) where
    mempty = Empty

{- |
  Vector is a group with addition as the operation and negation as the
  inverse.

Examples:

>>> v = vector $ (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> invert v
(-1 *^ 'x' + -1 *^ 'y')_1
>>> v <> invert v
_0

Properties:

prop> \v -> v <> invert v == (mempty :: Vector Integer Char)
prop> \v -> invert v <> v == (mempty :: Vector Integer Char)
prop> \v -> invert (invert v) == (v :: Vector Integer Char)
-}
instance (Num k, Eq k, Eq a, Graded a) => Group (Vector k a) where
    invert Empty = Empty
    invert (h :& ps) = invert h &: invert ps

{- |
  To ensure that the product of two vectors is also a vector, the
  product is distributed over the basis elements of the two vector.

Examples:

>>> v1 = vector $ (1 *^ "xy") +: (1 *^ "zw") +: Zero
>>> v2 = vector $ (1 *^ "xxyy") +: (1 *^ "zzww") +: Zero
>>> v1 * v2
(1 *^ "xyxxyy" + 1 *^ "zwxxyy" + 1 *^ "xyzzww" + 1 *^ "zwzzww")_6

Properties:

> \v1 v2 v3 -> v1 * (v2 * v3) == (v1 * v2) * (v3 :: Vector Integer [Char])
> \v1 v2 v3 -> v1 * (v2 + v3) == (v1 * v2) + (v1 * (v3 :: Vector Integer [Char]))
> \v1 v2 v3 -> (v1 + v2) * v3 == (v1 * v3) + (v2 * (v3 :: Vector Integer [Char]))
-}
instance
    ( Num k
    , Eq k
    , Eq a
    , Graded a
    , Monoid a
    )
    => Num (Vector k a)
    where
    (+) = (<>)

    negate = invert

    a * b = fromListV $ map (sum . map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListV a, toListV b]

    fromInteger n = fromInteger n &: Empty

    abs = error "abs not implemented for GradedAlgebra"

    signum = error "signum not implemented for GradedAlgebra"

----------------------------------------------------------------------

-- * Vector Functions

----------------------------------------------------------------------

{- |
  Returns a list of @ScalarProduct@ of a vector.

Examples:

>>> v = Zero &: (1 *^ 'x' +: 1 *^ 'y' +: Zero) &: Empty
>>> terms v
[1 *^ 'x',1 *^ 'y']
-}
terms :: Vector k a -> [ScalarProduct k a]
terms = concatMap toListS . toListV

{- |
  A list of basis elements of a vector.

Examples:

>>> v = vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: (1 *^ 'y') +: (2 *^ 'z') +: Zero
>>> basisElements v
"xyz"
-}
basisElements :: Vector k a -> [a]
basisElements = map basisElement . terms

-- | A class of types that can be cast to a vector.
class IsVector v where
    type VectorScalar v
    type VectorBasis v
    vector :: v -> Vector (VectorScalar v) (VectorBasis v)

{- |
  A @MultiSet@ is used to represent a commutative product and as a
  basis of an algebra.

Examples:

>>> vector $ MS.fromList "xy"
(1 *^ fromOccurList [('x',1),('y',1)])_2
-}
instance
    ( Eq a
    , Graded a
    , IsVector a
    , Num (VectorScalar a)
    , Eq (VectorScalar a)
    )
    => IsVector (MS.MultiSet a)
    where
    type VectorScalar (MS.MultiSet a) = VectorScalar a
    type VectorBasis (MS.MultiSet a) = MS.MultiSet a
    vector = vector . (1 *^)

{- |
  A list is often used to represent a product and as a basis of an
  algebra. Check @vectorFromList@ and @vectorFromNonDecList@ another
  way to get a vector from a list.

Examples:

>>> vector "xy"
(1 *^ "xy")_2
-}
instance
    ( Eq a
    , Graded a
    , IsVector a
    , Num (VectorScalar a)
    , Eq (VectorScalar a)
    )
    => IsVector [a]
    where
    type VectorScalar [a] = VectorScalar a
    type VectorBasis [a] = [a]
    vector = vector . (1 *^)

{- |
  A scalar product is cast to a vector with the same scalar and basis
  element. The implementation relies on the @IsVector@ instance of
  @Sum k a@.

Examples:

>>> vector $ 1 *^ 'x'
(1 *^ 'x')_1
-}
instance (Num k, Eq k, Eq a, Graded a) => IsVector (ScalarProduct k a) where
    type VectorScalar (ScalarProduct k a) = k
    type VectorBasis (ScalarProduct k a) = a
    vector = vector . (+: Zero)

{- |
  Construct a vector from a sum.

Examples:

>>> s1 = (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: (1 *^ 'y') +: Zero
>>> vector s1
(2 *^ 'x' + 2 *^ 'y')_1
>>> s2 = (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'x') +: ((-1) *^ 'y') +: (1 *^ 'z') +: Zero
>>> vector s2
(2 *^ 'x' + 1 *^ 'z')_1
-}
instance (Num k, Eq k, Eq a, Graded a) => IsVector (Sum k a) where
    type VectorScalar (Sum k a) = k
    type VectorBasis (Sum k a) = a
    vector Zero = Empty
    vector s@(Sum g _ _) = fromListV $ replicate (fromInteger g) Zero ++ [s]

-- | @Vector@ has a trivial @IsVector@ instance.
instance IsVector (Vector k a) where
    type VectorScalar (Vector k a) = k
    type VectorBasis (Vector k a) = a
    vector = id

{- |
  Construct a vector from a finite list of terms by ordering the terms
  according to the gradings.

!!! The list must be finite.

Examples:

>>> vectorFromList [1 *^ "x", 1 *^ "y", 3 *^ "xy", 1 *^ "x", 1 *^ "y"]
(2 *^ "x" + 2 *^ "y")_1 + (3 *^ "xy")_2
-}
vectorFromList
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [ScalarProduct k a]
    -> Vector k a
vectorFromList = vectorFromNonDecList . L.sortBy compareGrading
  where
    compareGrading x y = compare (grading x) (grading y)

{- |
  Construct a vector from a list of terms. The list may be infinite.

!!! The grading of terms in the list must be non-descreasing.

Examples:

>>> vectorFromNonDecList [1 *^ 'x', 1 *^ 'y', 1 *^ 'x', 1 *^ 'y']
(2 *^ 'x' + 2 *^ 'y')_1
>>> takeV 10 $ vectorFromNonDecList [1 *^ i | i <- [1..]]
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5 + 1 *^ 6 + 1 *^ 7 + 1 *^ 8 + 1 *^ 9)_1 + (1 *^ 10)_2
-}
vectorFromNonDecList
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => [ScalarProduct k a]
    -> Vector k a
vectorFromNonDecList = fromListV . map fromListS . groupByGrading . nDecList

{- |
  Takes a function from the basis to a vector space and extends it to
  a linear map.

!!! the function @linear f@ can receive only finite vectors.

Examples:

>>> f1 x = 1 *^ (x + 1)
>>> v1 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> linear f1 v1
(1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5)_1
>>> f2 x = vector $ (1 *^ x) +: (1 *^ (x + 1)) +: Zero
>>> v2 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> linear f2 v1
(1 *^ 1 + 2 *^ 2 + 2 *^ 3 + 2 *^ 4 + 1 *^ 5)_1
-}
linear
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k a
    -> Vector k b
linear f = mconcat . map (mconcat . map applyf . toListS) . toListV
  where
    applyf t = scaleV (scalar t) $ vector $ f $ basisElement t

{- |
  Takes a function from the basis to a vector space and extends it to
  a linear map.

!!! @f@ must respect the grading.

Examples:

>>> f (x:xs) = 1 *^ (2:xs)
>>> v1 = vectorFromList [1*^[1], 1*^ [1,1]]
>>> linearGraded f v1
(1 *^ [2])_1 + (1 *^ [2,1])_2
>>> v2 = vectorFromNonDecList [i*^(replicate i 1) | i <- [1..]]
>>> takeV 10 $ linearGraded f v2
(1 *^ [2])_1 + (2 *^ [2,1])_2 + (3 *^ [2,1,1])_3 + (4 *^ [2,1,1,1])_4 + (5 *^ [2,1,1,1,1])_5 + (6 *^ [2,1,1,1,1,1])_6 + (7 *^ [2,1,1,1,1,1,1])_7 + (8 *^ [2,1,1,1,1,1,1,1])_8 + (9 *^ [2,1,1,1,1,1,1,1,1])_9 + (10 *^ [2,1,1,1,1,1,1,1,1,1])_10
>>> v3 = vectorFromNonDecList [1*^i | i <- [0..]]
>>> g x = 1 *^ (x + 1)
>>> linearGraded g v3
*** Exception: Grading mismatch in a list of terms
...
-}
linearGraded
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k a
    -> Vector k b
linearGraded f = fromListV . map (fromListS . concatMap applyf . toListS) . toListV
  where
    applyf t = terms $ scaleV (scalar t) $ vector $ f $ basisElement t

{- |
  Takes a function from the basis to a vector space and extends it to
  a linear map.

!!! the function @f@ must be non-decreasing with respect to the grading, that is,
@(grading b1) <= (grading b2)@ implies @(min $ grading $ f b1) <= (min $ grading $ f b2)@,
where @min@ is the minimum of the grading of the terms in the image of @f@.

Examples:

>>> f x = 1 *^ (2:x)
>>> v1 = vectorFromList [1*^[1], 1*^ [1,1]]
>>> linearNonDec f v1
(1 *^ [2,1])_2 + (1 *^ [2,1,1])_3
>>> v2 = vectorFromNonDecList [i*^(replicate i 1) | i <- [1..]]
>>> takeV 10 $ linearNonDec f v2
(1 *^ [2,1])_2 + (2 *^ [2,1,1])_3 + (3 *^ [2,1,1,1])_4 + (4 *^ [2,1,1,1,1])_5 + (5 *^ [2,1,1,1,1,1])_6 + (6 *^ [2,1,1,1,1,1,1])_7 + (7 *^ [2,1,1,1,1,1,1,1])_8 + (8 *^ [2,1,1,1,1,1,1,1,1])_9 + (9 *^ [2,1,1,1,1,1,1,1,1,1])_10 + (10 *^ [2,1,1,1,1,1,1,1,1,1,1])_11
>>> v3 = vectorFromNonDecList [1*^i | i <- [0..]]
>>> g x = 1 *^ (x + 1)
>>> takeV 10 $ linearNonDec g v3
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5 + 1 *^ 6 + 1 *^ 7 + 1 *^ 8 + 1 *^ 9)_1 + (1 *^ 10)_2
-}
linearNonDec
    :: ( Num k
       , Eq k
       , Eq a
       , Eq b
       , Graded b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k a
    -> Vector k b
linearNonDec f = fromListV . addLevels . map (toListV . mconcat . map applyf . toListS) . toListV
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

{- |
  Take a function @f@ that maps basis elements to basis elements and
  extends it to a morphism of the algebra.

!!! The function @morphism f@ accepts only finite vectors.

Examples:

>>> f1 x = 1 *^ [x+1]
>>> v1 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphism f1 v1
(1 *^ [7,8])_2 + (1 *^ [9,10])_3
>>> f2 x = vectorFromList [1 *^ [x], 1 *^ [x+1]]
>>> v2 = vectorFromList [1 *^ [1, 2], 1 *^ [3, 4]]
>>> morphism f2 v2
(1 *^ [1,2] + 1 *^ [2,2] + 1 *^ [1,3] + 1 *^ [2,3] + 1 *^ [3,4] + 1 *^ [4,4] + 1 *^ [3,5] + 1 *^ [4,5])_2
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

>>> f1 x = 1 *^ [x+1]
>>> v1 = vectorFromList [1 *^ [6,7], 1 *^ [8, 9]]
>>> morphismGraded f1 v1
*** Exception: Grading mismatch between a term and a sum
...
>>> f2 x = if x > 0 && x < 9 then 1*^ [x + 1] else 1 *^ [x]
>>> v2 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphismGraded f2 v2
(1 *^ [7,8] + 1 *^ [9,9])_2
>>> v3 = vectorFromNonDecList [i *^ (replicate i 1) | i <- [1..]]
>>> takeV 10 $ morphismGraded f2 v3
(1 *^ [2])_1 + (2 *^ [2,2])_2 + (3 *^ [2,2,2])_3 + (4 *^ [2,2,2,2])_4 + (5 *^ [2,2,2,2,2])_5 + (6 *^ [2,2,2,2,2,2])_6 + (7 *^ [2,2,2,2,2,2,2])_7 + (8 *^ [2,2,2,2,2,2,2,2])_8 + (9 *^ [2,2,2,2,2,2,2,2,2])_9 + (10 *^ [2,2,2,2,2,2,2,2,2,2])_10
-}
morphismGraded
    :: ( Num k
       , Eq k
       , Functor f
       , Foldable f
       , Eq (f a)
       , Eq b
       , Graded b
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
(1 *^ [7,8])_2 + (1 *^ [9,10])_3
>>> f2 x = if x > 0 && x < 9 then 1*^ [x + 1] else 1 *^ [x]
>>> v2 = vectorFromList [1 *^ [6, 7], 1 *^ [8, 9]]
>>> morphismNonDec f2 v2
(1 *^ [7,8] + 1 *^ [9,9])_2
>>> v3 = vectorFromNonDecList [i *^ (replicate i 1) | i <- [1..]]
>>> takeV 10 $ morphismNonDec f2 v3
(1 *^ [2])_1 + (2 *^ [2,2])_2 + (3 *^ [2,2,2])_3 + (4 *^ [2,2,2,2])_4 + (5 *^ [2,2,2,2,2])_5 + (6 *^ [2,2,2,2,2,2])_6 + (7 *^ [2,2,2,2,2,2,2])_7 + (8 *^ [2,2,2,2,2,2,2,2])_8 + (9 *^ [2,2,2,2,2,2,2,2,2])_9 + (10 *^ [2,2,2,2,2,2,2,2,2,2])_10
-}
morphismNonDec
    :: ( Num k
       , Eq k
       , Functor f
       , Foldable f
       , Eq (f a)
       , Eq b
       , Graded b
       , Monoid b
       , IsVector v
       , VectorScalar v ~ k
       , VectorBasis v ~ b
       )
    => (a -> v)
    -> Vector k (f a)
    -> Vector k b
morphismNonDec f = linearNonDec $ product . fmap (vector . f)

{- |
  Change the coefficients in a vector using a function @f@ that takes
  the scalar and the basis element of a term and returns a new scalar.

Examples:

>>> f s x = s + 1
>>> v = vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
>>> renormalize f v
(2 *^ 'x' + 3 *^ 'y' + 4 *^ 'z' + 5 *^ 'w')_1
-}
renormalize
    :: ( Num k2
       , Eq k2
       , Eq a
       , Graded a
       )
    => (k1 -> a -> k2)
    -> Vector k1 a
    -> Vector k2 a
renormalize f = vectorFromNonDecList . map renormalizeTerm . terms
  where
    renormalizeTerm t = f (scalar t) (basisElement t) *^ basisElement t

{- |
  Scale a vector by a scalar.

Examples:

>>> v = vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
>>> scaleV 2 v
(2 *^ 'x' + 4 *^ 'y' + 6 *^ 'z' + 8 *^ 'w')_1
-}
scaleV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => k
    -> Vector k a
    -> Vector k a
scaleV s = renormalize (\s0 _ -> s * s0)

{- |
  Change the scalar of a vector.

Examples:

>>> f s = s + 1
>>> v = vector $ (1 *^ 'x') +: (2 *^ 'y') +: (3 *^ 'z') +: (4 *^ 'w') +: Zero
>>> rescale f v
(2 *^ 'x' + 3 *^ 'y' + 4 *^ 'z' + 5 *^ 'w')_1
-}
rescale :: (Num k1, Eq k1, Num k2, Eq k2, Eq a, Graded a) => (k1 -> k2) -> Vector k1 a -> Vector k2 a
rescale f = renormalize (\s _ -> f s)

{- |
  Extends a function @f@ that maps basis elements to scalars to a
  linear functional.

!!! The function @functional f@ accepts only finite vectors.

Examples:

>>> f x = fromInteger $ grading x
>>> v = vectorFromList [1 *^ "x", 2 *^ "y", 3 *^ "z", 4 *^ "ww"]
>>> functional f v
14
-}
functional
    :: ( Num k
       , Eq k
       , Eq a
       )
    => (a -> k)
    -> Vector k a
    -> k
functional f = sum . map (\t -> scalar t * f (basisElement t)) . terms

{- |
  The length of a vector is the number of terms in it.

Examples:

>>> v = vector $ (1 *^ 'x') +: (1 *^ 'y') +: (1 *^ 'z') +: (1 *^ 'w') +: Zero
>>> lengthV v
4

Properties:

prop> lengthV v == length (terms v :: [ScalarProduct Integer Char])
-}
lengthV :: Vector k a -> Int
lengthV = sum . map lengthS . toListV

{- |
  Take terms from a vector until the first term that does not satisfy
  the condition given by @f@.

Examples:

>>> f1 (i :*^ j) = j < 3
>>> v1 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> takeWhileV f1 v1
(1 *^ 1 + 1 *^ 2)_1
>>> f2 (i :*^ j) = j < 5
>>> v2 = vectorFromNonDecList [1 *^ i | i <- [1..]]
>>> takeWhileV f2 v2
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4)_1

Properties:

prop> takeWhileV (\_ -> True) v == (v :: Vector Integer Char)
prop> takeWhileV (\_ -> False) v == (mempty :: Vector Integer Char)
-}
takeWhileV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (ScalarProduct k a -> Bool)
    -> Vector k a
    -> Vector k a
takeWhileV f = vectorFromNonDecList . takeWhile f . terms

{- |
  Filter terms from a vector that satisfy the condition given by @f@.

Examples:

>>> f (_ :*^ j) = j `mod` 3 == 0
>>> v = vectorFromNonDecList [1 *^ i | i <- [1..]]
>>> takeV 10 $ filterV f v
(1 *^ 3 + 1 *^ 6 + 1 *^ 9)_1 + (1 *^ 12 + 1 *^ 15 + 1 *^ 18 + 1 *^ 21 + 1 *^ 24 + 1 *^ 27 + 1 *^ 30)_2

Properties:

prop> filterV (\_ -> True) v == (v :: Vector Integer Char)
prop> filterV (\_ -> False) v == (mempty :: Vector Integer Char)
-}
filterV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => (ScalarProduct k a -> Bool)
    -> Vector k a
    -> Vector k a
filterV f = fromListV . map (fromListS . filter f . toListS) . toListV

{- |
  Take the first @n@ terms from a vector.

Examples:

>>> v = vectorFromNonDecList [1 *^ i | i <- [1..]]
>>> takeV 10 v
(1 *^ 1 + 1 *^ 2 + 1 *^ 3 + 1 *^ 4 + 1 *^ 5 + 1 *^ 6 + 1 *^ 7 + 1 *^ 8 + 1 *^ 9)_1 + (1 *^ 10)_2

Properties:

prop> takeV (lengthV v) v == (v :: Vector Integer Char)
prop> takeV 0 v == (mempty :: Vector Integer Char)
-}
takeV
    :: ( Num k
       , Eq k
       , Eq a
       , Graded a
       )
    => Int
    -> Vector k a
    -> Vector k a
takeV n = vectorFromNonDecList . take n . terms

-----------------------------------------------------------------------------

-- * Tensor algebra

-----------------------------------------------------------------------------

instance
    ( Eq a
    , Graded a
    , IsVector a
    , Num (VectorScalar a)
    , Eq (VectorScalar a)
    , Eq b
    , Graded b
    , IsVector b
    , VectorScalar a ~ VectorScalar b
    )
    => IsVector (a, b)
    where
    type VectorScalar (a, b) = VectorScalar a
    type VectorBasis (a, b) = (a, b)
    vector = vector . (1 *^)

{- |
  Takes a product of basis elements and returns a tensor product of
  the corresponding basis vectors.

Examples:

>>> deshuffleCoproduct "xyz"
(1 *^ ("","xyz") + 1 *^ ("x","yz") + 1 *^ ("z","xy") + 1 *^ ("y","xz") + 1 *^ ("xz","y") + 1 *^ ("xy","z") + 1 *^ ("yz","x") + 1 *^ ("xyz",""))_3
-}
deshuffleCoproduct
    :: ( Eq a
       , Graded a
       , IsVector a
       , Num (VectorScalar a)
       , Eq (VectorScalar a)
       )
    => [a]
    -> Vector (VectorScalar a) ([a], [a])
deshuffleCoproduct =
    product
        . map (\b -> vector ([], [b]) + vector ([b], []))

{- |
  Takes a function with two arguments and extends it to a bilinear
  map.

!!! The function @bilinear f@ accepts only finite vectors.

Examples:

>>> f a b = 1 *^ [a + b]
>>> v1 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> v2 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> bilinear f v1 v2
(1 *^ [2] + 2 *^ [3] + 3 *^ [4] + 4 *^ [5] + 3 *^ [6] + 2 *^ [7] + 1 *^ [8])_1
-}
bilinear
    :: ( IsVector v
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
    -> Vector k a
    -> Vector k b
    -> Vector k c
bilinear f ps1 ps2 =
    linear (uncurry f . BF.bimap head head) $
        linearGraded ((1 *^) . (,[]) . (: [])) ps1 * linearGraded ((1 *^) . ([],) . (: [])) ps2

{- |
  Takes a function with two arguments and extends it to a bilinear
  map.

!!! The function @f@ must preserve the grading, that is,
@grading (f a b) = (grading a) + (grading b)@.

Examples:

>>> f1 a b = 1 *^ [a, b]
>>> f2 a b = 1 *^ [a + b]
>>> v1 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> v2 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> bilinearGraded f1 v1 v2
(1 *^ [1,1] + 1 *^ [2,1] + 1 *^ [1,2] + 1 *^ [3,1] + 1 *^ [2,2] + 1 *^ [1,3] + 1 *^ [4,1] + 1 *^ [3,2] + 1 *^ [2,3] + 1 *^ [1,4] + 1 *^ [4,2] + 1 *^ [3,3] + 1 *^ [2,4] + 1 *^ [4,3] + 1 *^ [3,4] + 1 *^ [4,4])_2
>>> bilinearGraded f2 v1 v2
*** Exception: Grading mismatch in a list of terms
...
-}
bilinearGraded
    :: ( IsVector v
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
    -> Vector k a
    -> Vector k b
    -> Vector k c
bilinearGraded f ps1 ps2 =
    linearGraded (uncurry f . BF.bimap head head) $
        linearGraded ((1 *^) . (,[]) . (: [])) ps1 * linearGraded ((1 *^) . ([],) . (: [])) ps2

{- |
  Takes a function with two arguments and extends it to a bilinear
  map.

!!! The function @f@ must be non-decreasing with respect to the
grading, that is, if
@(grading a) + (grading b) > (grading c) + (grading d)@,
then @grading (f a b) >= grading (f c d)@.

Examples:

>>> f a b = 1 *^ [a + b]
>>> v1 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> v2 = vector $ (1 *^ 1) +: (1 *^ 2) +: (1 *^ 3) +: (1 *^ 4) +: Zero
>>> bilinearNonDec f v1 v2
(1 *^ [2] + 2 *^ [3] + 3 *^ [4] + 4 *^ [5] + 3 *^ [6] + 2 *^ [7] + 1 *^ [8])_1
-}
bilinearNonDec
    :: ( IsVector v
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
    -> Vector k a
    -> Vector k b
    -> Vector k c
bilinearNonDec f ps1 ps2 =
    linearNonDec (uncurry f . BF.bimap head head) $
        linearGraded ((1 *^) . (,[]) . (: [])) ps1 * linearGraded ((1 *^) . ([],) . (: [])) ps2
