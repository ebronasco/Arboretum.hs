{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SymLists (
    Scalar,
    Basis,
    term,
    scalar,
    basisElement,
    basisTerm,
    scale,
    Sum,
    (+:),
    pattern (:+),
    Product (..),
    Algebra,
    PowerSeries (..),
) where


import Data.Group

import GradedList

data Term k a = Term k a deriving (Eq)

term :: (Scalar k, Eq a) => k -> a -> Term k a
term k a = Term k a

class (Num k, Eq k, Show k) => Scalar k

instance Scalar Int

instance Scalar Integer

class (Eq a, Show a, Graded a) => Basis a

instance Basis Int

instance Basis Integer

instance Basis Char

scalar :: (Scalar k, Eq a) => Term k a -> k
scalar (Term k _) = k

basisElement :: (Scalar k, Eq a) => Term k a -> a
basisElement (Term _ b) = b

scale :: (Scalar k, Eq a) => k -> Term k a -> Term k a
scale c1 (Term c2 b) = term (c1 * c2) b

basisTerm :: (Scalar k, Eq a) => a -> Term k a
basisTerm b = term (fromInteger 1) b

instance (Scalar k, Basis a) => Graded (Term k a) where
    grading = grading . basisElement

instance (Scalar k, Eq a, Show a) => Show (Term k a) where
    show (Term k b) = show k ++ " *^ " ++ show b

instance (Scalar k, Eq a, Semigroup a) => Semigroup (Term k a) where
    (Term k1 b1) <> (Term k2 b2) = term (k1 * k2) (b1 <> b2)

instance (Scalar k, Eq a, Monoid a) => Monoid (Term k a) where
    mempty = term (fromInteger 1) mempty

instance (Scalar k, Eq a, Group a) => Group (Term k a) where
    invert (Term k b) = term (negate k) (invert b)
                                                  

--------------- Sum ----------------

pattern (:+) :: (Scalar k, Eq a) => Term k a -> Sum k a -> Sum k a
pattern t :+ s <- Sum t s

data Sum k a = Sum (Term k a) (Sum k a) | Zero

fromListS :: (Scalar k, Eq a) => [Term k a] -> Sum k a
fromListS [] = Zero
fromListS (h : t) = h +: fromListS t

toListS :: (Scalar k, Eq a) => Sum k a -> [Term k a]
toListS Zero = []
toListS (h :+ t) = h : toListS t

instance (Scalar k, Eq a, Show a) => Show (Sum k a) where
    show ((Term k a) :+ Zero) = show k ++ " *^ " ++ show a
    show ((Term k a) :+ b) = show k ++ " *^ " ++ show a ++ " + " ++ show b
    show Zero = "0"


infixr 7 +:

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> (1, 1) +: [(1, 1), (1, 2)] :: [(Int, Int)]
[(2,1),(1,2)]
>>> (1, 3) +: [(1, 1), (1, 2)] :: [(Int, Int)]
[(1,3),(1,1),(1,2)]

Properties:

prop> (length $ t +: l) - 1 <= length (l :: [(Int, Int)])
-}
(+:) :: (Scalar k, Eq a) => Term k a -> Sum k a -> Sum k a
(+:) (Term 0 _) s = s
(+:) t s = case maybeAddTerm t s of
    Nothing -> Sum t s
    Just s' -> s'
  where
    maybeAddTerm t1 Zero = Nothing
    maybeAddTerm t1 (t2 :+ s2) =
        if t1_basis == (basisElement t2)
            then if scalar_sum /= 0 
                then Just $ Sum (term scalar_sum t1_basis) s2
                else Just s2
            else case maybeAddTerm t1 s2 of
                Nothing -> Nothing
                Just s2' -> Just $ Sum t2 s2'
      where
        t1_basis = basisElement t1
        scalar_sum = (scalar t1) + (scalar t2)

instance (Scalar k, Eq a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Scalar k, Eq a) => Monoid (Sum k a) where
    mempty = Zero

instance (Scalar k, Eq a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = (term (negate $ scalar t) (basisElement t)) +: (invert s)

instance (Scalar k, Eq a) => Eq (Sum k a) where
    s1 == s2 = (s1 <> (invert s2)) == Zero



--------------- Product ----------------

infixr 8 :*

data Product a = a :* (Product a) | One deriving (Eq)

fromListP :: [a] -> Product a
fromListP [] = One
fromListP (h : t) = h :* fromListP t

toListP :: Product a -> [a]
toListP One = []
toListP (h :* t) = h : toListP t

instance Graded a => Graded (Product a) where
    grading One = 0
    grading (a :* b) = grading a + grading b

instance Show a => Show (Product a) where
    show One = "1"
    show (a :* One) = show a
    show (a :* b) = show a ++ " * " ++ show b

instance Basis a => Basis (Product a)

instance Semigroup (Product a) where
    One <> a = a
    a <> One = a
    (a :* b) <> c = a :* (b <> c)

instance Monoid (Product a) where
    mempty = One


--------------- Algebra ----------------

type Algebra k a = Sum k (Product a)

instance (Scalar k, Eq a) => Num (Algebra k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = (term (fromInteger n) One) +: Zero

    abs = error "abs not implemented for Algebra"

    signum = error "signum not implemented for Algebra"

--------------- PowerSeries ----------------

infixr 6 :&

data PowerSeries a = a :& (PowerSeries a) | Empty deriving (Eq)

fromListPS :: [a] -> PowerSeries a
fromListPS [] = Empty
fromListPS (h : t) = h :& fromListPS t

toListPS :: PowerSeries a -> [a]
toListPS Empty = []
toListPS (h :& t) = h : toListPS t

instance (Show a) => Show (PowerSeries a) where
    show ps = show_ 0 ps
      where
        show_ n Empty = "_" ++ show n
        show_ n (a :& Empty) = "(" ++ show a ++ ")_" ++ show n
        show_ n (a :& b) = "(" ++ show a ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) b

instance (Semigroup a) => Semigroup (PowerSeries a) where
    Empty <> a = a
    a <> Empty = a
    (a :& b) <> (c :& d) = (a <> c) :& (b <> d)

instance (Monoid a) => Monoid (PowerSeries a) where
    mempty = Empty

instance (Group a) => Group (PowerSeries a) where
    invert Empty = Empty
    invert (a :& b) = (invert a) :& (invert b)


--------------- GradedAlgebra ----------------

type GradedAlgebra k a = PowerSeries (Algebra k a)

instance (Scalar k, Eq a) => Num (GradedAlgebra k a) where
    (+) = (<>)

    negate = invert

    a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListPS a, toListPS b]

    fromInteger n = (fromInteger n) :& Empty

    abs = error "abs not implemented for GradedAlgebra"

    signum = error "signum not implemented for GradedAlgebra"
