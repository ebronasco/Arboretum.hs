{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module VectorSpace (
    Scalar,
    Basis,
    Term,
    scalar,
    basisElement,
    basisTerm,
    scale,
    term,
    Sum (..),
    groupTerms,
    DirectProduct (..),
    gradeSum,
    GradedSum,
    Product (..),
) where

import Data.Foldable
import Data.Group
import GradedList

type Term k a = (k, a)

class (Num k, Eq k, Show k) => Scalar k

instance Scalar Int

instance Scalar Integer

class (Eq a, Show a, Graded a) => Basis a

instance Basis Int

instance Basis Integer

instance Basis Char

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

infixr 7 :+

data Sum k a = (Term k a) :+ (Sum k a) | Zero

instance (Show k, Show a) => Show (Sum k a) where
    show ((k, a) :+ Zero) = show k ++ " *^ " ++ show a
    show ((k, a) :+ b) = show k ++ " *^ " ++ show a ++ " + " ++ show b
    show Zero = "0"

{- | Internal function. Adds a term to a finite list. Grading ignorant.

Examples:

>>> addTerm (1, 1) [(1, 1), (1, 2)] :: [(Int, Int)]
[(2,1),(1,2)]
>>> addTerm (1, 3) [(1, 1), (1, 2)] :: [(Int, Int)]
[(1,3),(1,1),(1,2)]

Properties:

prop> (length $ addTerm t l) - 1 <= length (l :: [(Int, Int)])
-}
addTerm :: (Scalar k, Basis a) => Term k a -> Sum k a -> Sum k a
addTerm t Zero = t :+ Zero
addTerm t (t0 :+ ts) = case (basisElement t0) == basis_t of
    True -> (term (scalar t + scalar t0) basis_t) :+ ts
    False -> t0 :+ (addTerm t ts)
  where
    basis_t = basisElement t

instance (Scalar k, Basis a) => Semigroup (Sum k a) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    s1 <> (t :+ s2) = (addTerm t s1) <> s2

instance (Scalar k, Basis a) => Monoid (Sum k a) where
    mempty = Zero

instance (Scalar k, Basis a) => Group (Sum k a) where
    invert Zero = Zero
    invert (t :+ s) = (term (negate $ scalar t) (basisElement t)) :+ (invert s)

instance (Scalar k, Basis a) => Eq (Sum k a) where
    s1 == s2 = (s1 <> (invert s2)) == Zero

sumToList :: (Scalar k, Basis a) => Sum k a -> [Term k a]
sumToList Zero = []
sumToList (t :+ s) = t : sumToList s

listToSum :: (Scalar k, Basis a) => [Term k a] -> Sum k a
listToSum [] = Zero
listToSum (t : ts) = t :+ listToSum ts

groupTerms :: (Scalar k, Basis a) => Sum k a -> Sum k a
groupTerms Zero = Zero
groupTerms (t :+ s) = addTerm t (groupTerms s)

mapSum :: (Basis a, Basis b) => (a -> b) -> Sum k a -> Sum k b
mapSum f Zero = Zero
mapSum f (t :+ s) = (term (scalar t) (f $ basisElement t)) :+ (mapSum f s)


infixr 6 :&

data DirectProduct a = a :& (DirectProduct a) | Empty deriving (Foldable)

instance (Show a) => Show (DirectProduct a) where
    show Empty = "1"
    show dp =
        foldr
            ( \t acc ->
                "("
                    ++ show t
                    ++ ")"
                    ++ case acc of
                        "" -> ""
                        _ -> " * " ++ acc
            )
            ""
            dp

instance (Semigroup a) => Semigroup (DirectProduct a) where
    Empty <> a = a
    a <> Empty = a
    (a :& b) <> (c :& d) = (a <> c) :& (b <> d)

instance (Monoid a) => Monoid (DirectProduct a) where
    mempty = Empty

instance (Group a) => Group (DirectProduct a) where
    invert Empty = Empty
    invert (a :& b) = (invert a) :& (invert b)

instance (Eq a) => Eq (DirectProduct a) where
    Empty == Empty = True
    (a :& b) == (c :& d) = (a == c) && (b == d)
    _ == _ = False

listToDProd :: [a] -> DirectProduct a
listToDProd [] = Empty
listToDProd (h : t) = h :& listToDProd t

type GradedSum k a = DirectProduct (Sum k a)

gradeSum :: (Scalar k, Basis a) => Sum k a -> GradedSum k a
gradeSum Zero = Empty
gradeSum s = listToDProd $ map listToSum $ groupByGrading $ sumToList s

infixr 8 :*

data Product a = a :* (Product a) | One deriving (Foldable)

instance (Show a) => Show (Product a) where
    show One = "1"
    show p =
        foldr
            ( \t acc ->
                 show t
                    ++ case acc of
                        "" -> ""
                        _ -> " * " ++ acc
            )
            ""
            p

instance (Basis a) => Semigroup (Product a) where
    One <> a = a
    a <> One = a
    (a :* b) <> c = a :* (b <> c)

instance (Basis a) => Monoid (Product a) where
    mempty = One

instance (Basis a) => Eq (Product a) where
    One == One = True
    (a :* b) == (c :* d) = (a == c) && (b == d)
    _ == _ = False
