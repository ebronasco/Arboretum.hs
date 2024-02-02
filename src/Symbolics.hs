{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

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
    Term(..),
    basisTerm,
    scale,
    term,

    -- * Graded vector space
--    VectorSpace,
    vector,
    vectorG,
    basisVector,
    basisVectorG,
    terms,
    mapV,
    mapVG,
    linear,
--    linearG,
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

    Sum,
    pattern (:+),
    PowerSeries(..),

    -- * Debug
    (+:),
) where

import Data.Group
import qualified Data.List as L (
    intercalate,
    sortBy,
 )
import GradedList (
    Graded,
    Grading,
    distributeLists,
    distributeGradedLists,
    grading,
    groupByGrading,
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
instance Arbitrary (VectorSpace Integer Integer) where
   arbitrary = vector <$> (arbitrary :: Gen [Term Integer Integer])
:}
-}

-----------------------------------------------------------------------------

-- * Graded vector space

-----------------------------------------------------------------------------

class (Num k, Eq k, Show k) => Scalar k

instance Scalar Int

instance Scalar Integer

class (Eq a, Show a, Graded a) => Basis a

instance Basis Int

instance Basis Integer

instance Basis a => Basis [a]

--------------- Term ----------------

-- | A term is defined to be a pair of a scalar (@Num@) and a product of basis elements.
data Term k a = Term
    { scalar :: k
    , basisElement :: [a]
    }
    deriving (Eq)

instance (Show k, Show a) => Show (Term k a) where
    show (Term s b) = (show s) ++ " *^ " ++ (show b)

-- | Take a functions and extend it to a morphism.
instance Functor (Term k) where
    fmap f (Term s b) = Term s (map f b)

-- | Choose the product semigroup for the scalar type.
instance Num k => Semigroup (Term k a) where
    (Term s1 b1) <> (Term s2 b2) = Term (s1 * s2) (b1 <> b2)

instance Num k => Monoid (Term k a) where
    mempty = Term 1 mempty

term :: (Scalar k, Basis a) => k -> [a] -> Term k a
term = Term

scale :: (Scalar k, Basis a) => k -> Term k a -> Term k a
scale c1 t = term (c1 * (scalar t)) $ basisElement t

basisTerm :: (Scalar k, Basis a) => [a] -> Term k a
basisTerm x = term (fromInteger 1) x

instance (Scalar k, Basis a) => Graded (Term k a) where
    grading = grading . basisElement


--------------- Sum ----------------

pattern (:+) :: Term k a -> Sum k a -> Sum k a
pattern t :+ s <- Sum t s

-- | A sum is assumed to have a finite number of terms.
data Sum k a = Sum (Term k a) (Sum k a) | Zero

fromListS :: (Scalar k, Basis a) => [Term k a] -> Sum k a
fromListS [] = Zero
fromListS (h : t) = h +: fromListS t

toListS :: Sum k a -> [Term k a]
toListS Zero = []
toListS (h :+ s) = h : toListS s

instance (Show k, Show a) => Show (Sum k a) where
    show (t :+ Zero) = show t
    show (t :+ s) = show t ++ " + " ++ show s
    show Zero = "0"

infixr 7 +:

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> (term 1 [1]) +: (fromListS [term 1 [1], term 1 [2]])
(2 *^ [1] + 1 *^ [2])
>>> (term 1 [3]) +: (fromListS [(1, 1), (1, 2)])
(1 *^ [3] + 1 *^ [1] + 1 *^ [2])

Properties:

prop> (length $ t +: l) - 1 <= length (l :: Sum Integer Integer)
-}
(+:) :: (Scalar k, Basis a) => Term k a -> Sum k a -> Sum k a
(+:) (Term 0 _) s = s
(+:) t s = case maybeAddTerm t s of
    Nothing -> Sum t s
    Just s' -> s'
  where
    maybeAddTerm t1 Zero = Nothing
    maybeAddTerm t1 (t2 :+ s2) =
        if t1_basis == (basisElement t2)
            then
                if scalar_sum /= 0
                    then Just $ Sum (term scalar_sum t1_basis) s2
                    else Just s2
            else case maybeAddTerm t1 s2 of
                Nothing -> Nothing
                Just s2' -> Just $ Sum t2 s2'
      where
        t1_basis = basisElement t1
        scalar_sum = (scalar t1) + (scalar t2)

instance (Scalar k, Basis a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Scalar k, Basis a) => Monoid (Sum k a) where
    mempty = Zero

instance (Scalar k, Basis a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = (term (negate $ scalar t) (basisElement t)) +: (invert s)

instance (Scalar k, Basis a) => Eq (Sum k a) where
    s1 == s2 = (s1 <> (invert s2)) == Zero

instance (Scalar k, Basis a) => Num (Sum k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = (term (fromInteger n) []) +: Zero

    abs = error "abs not implemented for Algebra"

    signum = error "signum not implemented for Algebra"


--------------- PowerSeries ----------------

infixr 6 :&

-- | A power series can have infinite number of terms.
data PowerSeries k a = (Sum k a) :& (PowerSeries k a) | Empty deriving (Eq)

fromListPS :: [Sum k a] -> PowerSeries k a
fromListPS [] = Empty
fromListPS (h : t) = h :& fromListPS t

toListPS :: PowerSeries k a -> [Sum k a]
toListPS Empty = []
toListPS (h :& ps) = h : toListPS ps

instance (Show k, Show a) => Show (PowerSeries k a) where
    show ps = show_ 0 ps
      where
        show_ n Empty = "_" ++ show n
        show_ n (h :& Empty) = "(" ++ show h ++ ")_" ++ show n
        show_ n (h :& ps) = "(" ++ show h ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) ps

instance (Scalar k, Basis a) => Semigroup (PowerSeries k a) where
    Empty <> ps = ps
    ps <> Empty = ps
    (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) :& (ps1 <> ps2)

instance (Scalar k, Basis a) => Monoid (PowerSeries k a) where
    mempty = Empty

instance (Scalar k, Basis a) => Group (PowerSeries k a) where
    invert Empty = Empty
    invert (h :& ps) = (invert h) :& (invert ps)

instance (Scalar k, Basis a) => Num (PowerSeries k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListPS a, toListPS b]

    fromInteger n = (fromInteger n) :& Empty

    abs = error "abs not implemented for GradedAlgebra"

    signum = error "signum not implemented for GradedAlgebra"


--------------- PowerSeries Functions ----------------

{- |
    Vectors are nested lists of terms. The outer list is @[l0, l1, l2, ..]@
    where @li@ is a list of terms with grading @i@.

    /NOT OPTIMAL: a vector with a single term with grading @N@ will have @N - 1@ empty lists in it./

    /Note: list are used because graphs are not @Ord@ and lists can be infinite./
-}
--data VectorSpace k a = Vector {unVector :: [Grading (Term k a)]}

{- | A flat list of terms.
Examples:

>>> terms $ Vector [[], [term 1 [1], term 1 [2]]]
[1 *^ [1],1 *^ [2]]

Properties:

prop> terms (Vector ts) == concat ts
-}
terms :: (Scalar k, Basis a) => PowerSeries k a -> [Term k a]
terms = (concatMap toListS) . toListPS

-- -- | Only finite vectors can be compared.
-- instance (Scalar k, Basis a) => Eq (VectorSpace k a) where
--     v1 == v2 = (== 0) $ lengthV $ (<> v2) $ invert v1

-- instance (Scalar k, Basis a) => Show (VectorSpace k a) where
--     show v = "(" ++ (L.intercalate " + " $ map show $ terms v) ++ ")"

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> addTerm (term 1 [1]) [term 1 [1], term 1 [2]]
[2 *^ [1],1 *^ [2]]
>>> addTerm (term 1 [3]) [term 1 [1], term 1 [2]]
[1 *^ [3],1 *^ [1],1 *^ [2]]

Properties:

prop> (length $ addTerm t l) - 1 <= length l
-}
-- addTerm :: (Scalar k, Basis a) => Term k a -> [Term k a] -> [Term k a]
-- addTerm t ts = case (span findTerm ts) of
--     (pre, []) -> t : pre
--     (pre, t0 : post) -> pre ++ (addToTerm t0) ++ post
--   where
--     findTerm t0 = (basisElement t0) /= (basisElement t)
--     addToTerm t0 =
--         if scalarSum /= 0
--             then [term scalarSum $ basisElement t]
--             else []
--       where
--         scalarSum = (scalar t) + (scalar t0)

{- | Group terms with the same basis element. Grading ignorant.

Examples:

>>> groupTerms [term 1 [1], term 1 [2], term 1 [1], term 1 [2]]
[2 *^ [1],2 *^ [2]]
>>> groupTerms [term 1 [1], term 1 [2], term 1 [1], term 1 [2], term 1 [3]]
[2 *^ [1],2 *^ [2],1 *^ [3]]

Properties:

prop> (length $ groupTerms l) <= length l
-}
-- groupTerms :: (Scalar k, Basis a) => Sum k a -> [Term k a]
-- groupTerms = foldr (+:) mempty

{- | Construct a vector from a list of terms. The list must be finite.

Examples:

>>> vector [term 1 [1], term 1 [2], term 1 [1], term 1 [2]]
(2 *^ [1] + 2 *^ [2])
>>> vector [term 1 [1], term 1 [2], term 1 [1], term (-1) [2], term 1 [3]]
(2 *^ [1] + 1 *^ [3])
-}
vector :: (Scalar k, Basis a) => [Term k a] -> PowerSeries k a
vector = vectorG . (L.sortBy compareGrading)
  where
    compareGrading x y = compare (grading x) (grading y)

{- |  Construct a vector from a list of terms. The list must be graded with finite number of terms having the same grading. The list itself may be infinite.

Examples:

>>> vectorG [term 1 [1], term 1 [2], term 1 [1], term 1 [2]]
(2 *^ [1] + 2 *^ [2])
>>> takeV 10 $ vectorG [term 1 [i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5] + 1 *^ [6] + 1 *^ [7] + 1 *^ [8] + 1 *^ [9] + 1 *^ [10])
-}
vectorG :: (Scalar k, Basis a) => [Term k a] -> PowerSeries k a
vectorG = (fromListPS) . (map fromListS) . groupByGrading

-- | The same as @vector@ but with basis elements instead of terms.
basisVector :: (Scalar k, Basis a) => [[a]] -> PowerSeries k a
basisVector = vector . (map basisTerm)

-- | The same as @vectorG@ but with basis elements instead of terms.
basisVectorG :: (Scalar k, Basis a) => [[a]] -> PowerSeries k a
basisVectorG = vectorG . (map basisTerm)

{- | Vector space is a semigroup with addition as the operation.

Examples:

>>> vector [term 1 [1], term 1 [2]] <> (vector [term 1 [1], term 1 [2], term 2 [3]])
(2 *^ [3] + 2 *^ [1] + 2 *^ [2])

Properties:

prop> v1 <> v2 == (v2 <> v1 :: VectorSpace Integer Integer)
-}
-- instance (Scalar k, Basis a) => Semigroup (VectorSpace k a) where
--     v1 <> v2 = Vector $ zipWithDefault addGradings (unVector v1) (unVector v2)
--       where
--         zipWithDefault _ [] [] = []
--         zipWithDefault f [] (e : t) = (f [] e) : zipWithDefault f [] t
--         zipWithDefault f (e : t) [] = (f e []) : zipWithDefault f t []
--         zipWithDefault f (e1 : t1) (e2 : t2) = (f e1 e2) : zipWithDefault f t1 t2
-- 
--         addGradings ts1 ts2 = foldr addTerm ts1 ts2

{- | Vector space is a monoid with addition as the operation and the empty vector as the identity.

Examples:

>>> mempty :: VectorSpace Integer Integer
()
>>> vector [term 1 [1], term 1 [2]] <> mempty
(1 *^ [1] + 1 *^ [2])

Properties:

prop> v <> mempty == (v :: VectorSpace Integer Integer)
-}
-- instance (Scalar k, Basis a) => Monoid (VectorSpace k a) where
--     mempty = Vector []

{- | Vector space is a group with addition as the operation and negation as the inverse.

Examples:

>>> invert $ vector [term 1 [1], term 1 [2]]
(-1 *^ [1] + -1 *^ [2])
>>> vector [term 1 [1], term 1 [2]] <> invert (vector [term 1 [1], term 1 [2]])
()

Properties:

prop> v <> invert v == (mempty :: VectorSpace Integer Integer)
prop> invert v <> v == (mempty :: VectorSpace Integer Integer)
prop> invert (invert v) == (v :: VectorSpace Integer Integer)
-}
-- instance (Scalar k, Basis a) => Group (VectorSpace k a) where
--     invert = renormalize (\s _ -> negate s)

{- | Vector space is an instance of the @Num@ class since both addition and multiplication are defined on it. To ensure that the product of two vectors is also a vector, the product is distributed over the basis elements of the two vectors.

Examples:

>>> (vector [term 1 [1, 2], term 1 [3, 4]]) * (vector [term 1 [11, 12], term 1 [13, 14]])
(1 *^ [1,2,11,12] + 1 *^ [3,4,11,12] + 1 *^ [1,2,13,14] + 1 *^ [3,4,13,14])
-}
-- instance (Scalar k, Basis a) => Num (VectorSpace k a) where
--     (+) = (<>)
-- 
--     v1 * v2 =
--         Vector $
--             map (map mconcat) $
--                 distributeGradedLists $
--                     map unVector $
--                         [v1, v2]
-- 
--     -- \| Absolute value of a vector makes no sense.
--     abs = id
-- 
--     -- \| Signum of a vector makes no sense either.
--     signum _ = 1
-- 
--     -- \| Inject integers into the tensor algebra.
--     fromInteger i = vector [term (fromInteger i) []]
-- 
--     negate = invert




{- | Extends a function @f@ that maps basis elements to basis elements to a linear map. The resulting function accepts only finite vectors.

Examples:

>>> mapV (\[b]-> [b + 1]) $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
(1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5])

Properties:

prop> mapV id v == (v :: VectorSpace Integer Integer)

as well as @(mapV f (fmap g v)) == (map (f . g) v)@ and @(mapV f (v1 <> v2)) == ((mapV f v1) <> (mapV f v2))@.

/__TODO:__ add property-tests for the last two properties above. Difficulty: how to generate functions that are monotonically increasing with respect to the grading? Use suchThat function of QuickCheck./
-}
mapV :: (Scalar k, Basis a, Basis b) => ([a] -> [b]) -> PowerSeries k a -> PowerSeries k b
mapV f = vector . (map $ fmap_ f) . terms
  where fmap_ g t = term (scalar t) $ g $ basisElement t

{- | The same as @fmap@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(grading $ f b1) <= (grading $ f b2)@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 10 $ mapVG (\[x] -> [x*10]) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [10] + 1 *^ [20] + 1 *^ [30] + 1 *^ [40] + 1 *^ [50] + 1 *^ [60] + 1 *^ [70] + 1 *^ [80] + 1 *^ [90] + 1 *^ [100])
-}
mapVG :: (Scalar k, Basis a, Basis b) => ([a] -> [b]) -> PowerSeries k a -> PowerSeries k b
mapVG f = vectorG . (map $ fmap_ f) . terms
  where fmap_ g t = term (scalar t) $ g $ basisElement t

{- | Takes a function from the basis to a vector space and extends it to a linear map. The resulting function accepts only finite vectors.

!!! The function @f@ must preserve the grading.

Examples:

>>> linear (\[b] -> vector [term 1 [b], term 1 [b + 1]]) $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
(1 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4] + 1 *^ [5])
-}
linear
    :: ( Scalar k
       , Basis a
       , Basis b
       )
    => ([a] -> PowerSeries k b)
    -> PowerSeries k a
    -> PowerSeries k b
linear f = sum . (map $ sum . (map applyf) . toListS) . toListPS
  where
    applyf t = scaleV (scalar t) $ f $ basisElement t

{- | The same as @linear@, but the function @f@ must be monotonically increasing with respect to the grading, that is,

@(grading b1) <= (grading b2)@ implies @(min $ grading $ f b1) <= (min $ grading $ f b2)@.

The resulting function accepts infinite vectors.

Examples:

>>> takeV 10 $ linearG (\[b] -> basisVectorG [[i] | i <- [b..]]) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 2 *^ [2] + 3 *^ [3] + 4 *^ [4] + 5 *^ [5] + 6 *^ [6] + 7 *^ [7] + 8 *^ [8] + 9 *^ [9] + 10 *^ [10])
-}
-- linearG
--     :: ( Scalar k
--        , Basis a
--        , Basis b
--        )
--     => ([a] -> PowerSeries k b)
--     -> PowerSeries k a
--     -> PowerSeries k b
-- linearG f = vectorG . (concatMap applyf) . terms
--   where
--     applyf t = terms $ scaleV (scalar t) $ f $ basisElement t

{- | Take a function @f@ that maps basis elements to basis elements and extends it to a morphism of the tensor algebra.

Examples:

>>> morphism (\b -> basisVector [[b + 1]]) $ vector [term 1 [1, 2, 3, 4], term 1 [11, 12, 13, 14]]
(1 *^ [2,3,4,5] + 1 *^ [12,13,14,15])
-}
morphism
    :: ( Scalar k
       , Basis a
       , Basis b
       )
    => (a -> PowerSeries k b)
    -> PowerSeries k a
    -> PowerSeries k b
morphism f = linear $ product . (map f)

{- | Change the coefficients in a vector using a function @f@ that takes the scalar and the basis element of a term and returns a new scalar.

Examples:

>>> renormalize (\s b -> s + 1) $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
(2 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4])
-}
renormalize
    :: ( Scalar k1
       , Scalar k2
       , Basis a
       )
    => (k1 -> [a] -> k2)
    -> PowerSeries k1 a
    -> PowerSeries k2 a
renormalize f = vectorG . (map $ renormalizeTerm) . terms
  where
    renormalizeTerm t = term (f (scalar t) (basisElement t)) $ basisElement t

{- | Scale a vector by a scalar.

Examples:

>>> scaleV 2 $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
(2 *^ [1] + 2 *^ [2] + 2 *^ [3] + 2 *^ [4])
-}
scaleV :: (Scalar k, Basis a) => k -> PowerSeries k a -> PowerSeries k a
scaleV s = renormalize (\s0 _ -> s * s0)

{- | Extends a function @f@ that maps basis elements to scalars to a linear functional. The resulting function accepts only finite vectors.

Examples:

>>> functional (\b -> fromInteger $ grading b) $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
4
-}
functional :: (Scalar k, Basis a) => ([a] -> k) -> PowerSeries k a -> k
functional f = sum . (map $ \t -> (scalar t) * (f $ basisElement t)) . terms

{- | The length of a vector is the number of terms in it.

Examples:

>>> lengthV $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
4

Properties:

prop> lengthV v == length (terms v :: [Term Integer Integer])
-}
lengthV :: (Scalar k, Basis a) => PowerSeries k a -> k
lengthV = functional (\_ -> 1)

{- | Take terms from a vector until the first term that does not satisfy the condition given by @f@.

Examples:

>>> takeWhileV (\(Term i [j]) -> j < 3) $ vector [term 1 [1], term 1 [2], term 1 [3], term 1 [4]]
(1 *^ [1] + 1 *^ [2])
>>> takeWhileV (\(Term i [j]) -> j < 5) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4])

Properties:

prop> takeWhileV (\_ -> True) v == (v :: VectorSpace Integer Integer)
prop> takeWhileV (\_ -> False) v == (mempty :: VectorSpace Integer Integer)
-}
takeWhileV :: (Scalar k, Basis a) => (Term k a -> Bool) -> PowerSeries k a -> PowerSeries k a
takeWhileV f = vectorG . (takeWhile f) . terms

{- | Filter terms from a vector that satisfy the condition given by @f@.

Examples:

>>> takeV 10 $ filterV (\(Term _ [j]) -> j `mod` 3 == 0) $ basisVectorG [[i] | i <- [1..]]
(1 *^ [3] + 1 *^ [6] + 1 *^ [9] + 1 *^ [12] + 1 *^ [15] + 1 *^ [18] + 1 *^ [21] + 1 *^ [24] + 1 *^ [27] + 1 *^ [30])

Properties:

prop> filterV (\_ -> True) v == (v :: VectorSpace Integer Integer)
prop> filterV (\_ -> False) v == (mempty :: VectorSpace Integer Integer)
-}
filterV :: (Scalar k, Basis a) => (Term k a -> Bool) -> PowerSeries k a -> PowerSeries k a
filterV f = fromListPS . (map $ fromListS . (filter f) . toListS) . toListPS

{- | Take the first @n@ terms from a vector.

Examples:

>>> takeV 10 $ basisVectorG [[i] | i <- [1..]]
(1 *^ [1] + 1 *^ [2] + 1 *^ [3] + 1 *^ [4] + 1 *^ [5] + 1 *^ [6] + 1 *^ [7] + 1 *^ [8] + 1 *^ [9] + 1 *^ [10])

Properties:

prop> takeV (lengthV v) v == (v :: VectorSpace Integer Integer)
prop> takeV 0 v == (mempty :: VectorSpace Integer Integer)
-}
takeV :: (Scalar k, Basis a) => Int -> PowerSeries k a -> PowerSeries k a
takeV n = vectorG . (take n) . terms

{- | Takes a product of basis elements and returns a tensor product of the corresponding basis vectors.

Examples:

>>> tensorCoproduct [1,2,3]
(1 *^ [[1,2,3],[]] + 1 *^ [[1,2],[3]] + 1 *^ [[1,3],[2]] + 1 *^ [[1],[2,3]] + 1 *^ [[2,3],[1]] + 1 *^ [[2],[1,3]] + 1 *^ [[3],[1,2]] + 1 *^ [[],[1,2,3]])
-}
tensorCoproduct :: (Scalar k, Basis a) => [a] -> PowerSeries k [a]
-- tensorCoproduct = product . (map (\b -> basisVector [([b],[]), ([],[b])]))
tensorCoproduct = vector . (map (term (fromInteger 1))) . listCoproduct
  where
    listCoproduct [] = [[[], []]] -- sum of tensor products of products
    listCoproduct (b : bs) =
        ( map
            (zipWith (<>) [[b], []])
            tailCoproduct
        )
            ++ ( map
                    (zipWith (<>) [[], [b]])
                    tailCoproduct
               )
      where
        tailCoproduct = listCoproduct bs

-- TODO: define a product class with projections from and injections to the tensor algebra? This way the num and morphisms can be defined through those.
