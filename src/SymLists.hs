{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module SymLists (
    Scalar,
    Basis,
    Product,
    pattern (:*),
    Sum (Zero),
    leadingCoeff,
    leadingElement,
    PowerSeries (..),
    Algebra,
    Algebra2,
    GradedAlgebra,
    GradedAlgebra2,
) where

import Data.Group
import GradedList


class (Num sc, Eq sc, Show sc) => Scalar sc

instance Scalar Int

instance Scalar Integer

class (Eq b, Show b) => Basis b

instance Basis Int

instance Basis Integer

instance Basis Char

--------------- Product ----------------

pattern (:*) :: (Basis b) => b -> Product b -> Product b
pattern t :* s <- Product t s

data Product b = Product b (Product b) | One deriving (Eq)

(*:) :: (Basis b) => b -> Product b -> Product b
(*:) = Product

type family ProductBasis p where
    ProductBasis (Product b) = b
    ProductBasis b = b

class IsProduct p where
    toProduct :: p -> Product (ProductBasis p)

instance (Basis b, ProductBasis b ~ b) => IsProduct b where
    toProduct b = b *: One

instance (Basis b) => IsProduct (Product b) where
    toProduct = id

fromListP :: (Basis b) => [b] -> Product b
fromListP [] = One
fromListP (h : t) = h *: fromListP t

toListP :: Product b -> [b]
toListP One = []
toListP (h :* t) = h : toListP t

instance (Graded b) => Graded (Product b) where
    grading One = 0
    grading (t :* p) = grading t + grading p

instance (Show b) => Show (Product b) where
    show One = "1"
    show (t :* One) = show t
    show (t :* p) = show t ++ " * " ++ show p

instance Semigroup (Product b) where
    One <> p = p
    p <> One = p
    (t :* p1) <> p2 = t *: (p1 <> p2)

instance Monoid (Product b) where
    mempty = One

--------------- Term (internal) ----------------

data Term sc b = sc :*^ (Product b) deriving (Eq)

(*^) :: (Scalar sc, Eq b, ProductBasis p ~ b, IsProduct p) => sc -> p -> Term sc b
sc *^ p = sc :*^ (toProduct p)

instance (Scalar sc, Eq b, Show b) => Show (Term sc b) where
    show (sc :*^ b) = show sc ++ " *^ " ++ show b

-- Choose the Product monoid of Num for the scalars.
instance (Scalar sc, Eq b, Semigroup b) => Semigroup (Term sc b) where
    (sc1 :*^ b1) <> (sc2 :*^ b2) = (sc1 * sc2) *^ (b1 <> b2)

instance (Scalar sc, Eq b) => Monoid (Term sc b) where
    mempty = (fromInteger 1) *^ One

instance (Scalar sc, Eq b, Group b) => Group (Term sc b) where
    invert (sc :*^ b) = (negate sc) *^ (invert b)

--------------- Sum ----------------

pattern (:+) :: (Scalar sc, Eq b) => Term sc b -> Sum sc b -> Sum sc b
pattern t :+ s <- Sum t s

data Sum sc b = Sum (Term sc b) (Sum sc b) | Zero

type family SumScalar s where
    SumScalar (Sum sc b) = sc
    SumScalar s = Integer

class IsSum s where
    toSum :: s -> Sum (SumScalar s) (ProductBasis s)

instance IsSum (Product b) where
    toSum p = ((fromInteger 1) *^ p) +: Zero

instance (IsProduct b) => IsSum b where
    toSum = toSum . toProduct

instance IsSum (Sum sc b) where
    toSum = id

leadingCoef :: (Scalar sc, Eq b) => Sum sc b -> sc
leadingCoef Zero = 0
leadingCoef ((sc :*^ _) :+ _) = sc

leadingElem :: (Scalar sc, Eq b) => Sum sc b -> Product b
leadingElem Zero = One
leadingElem ((_ :*^ b) :+ _) = b

instance (Scalar sc, Eq b, Show b) => Show (Sum sc b) where
    show ((sc :*^ b) :+ Zero) = show sc ++ " *^ " ++ show b
    show ((sc :*^ b) :+ s) = show sc ++ " *^ " ++ show b ++ " + " ++ show s
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
(+:) :: (Scalar sc, Eq b) => Term sc b -> Sum sc b -> Sum sc b
(+:) (0 :*^ _) t = t
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

instance (Scalar sc, Eq b) => Semigroup (Sum sc b) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Scalar sc, Eq b) => Monoid (Sum sc b) where
    mempty = Zero

instance (Scalar sc, Eq b) => Group (Sum sc b) where
    invert Zero = Zero
    invert (t :+ s) = (term (negate $ scalar t) (basisElement t)) +: (invert s)

instance (Scalar sc, Eq b) => Eq (Sum sc b) where
    s1 == s2 = (s1 <> (invert s2)) == Zero

--------------- PowerSeries ----------------

infixr 6 :&

data PowerSeries a = a :& (PowerSeries a) | Empty deriving (Eq)

fromListPS :: [a] -> PowerSeries a
fromListPS [] = Empty
fromListPS (h : t) = h :& fromListPS t

toListPS :: PowerSeries a -> [a]
toListPS Empty = []
toListPS (h :& ps) = h : toListPS ps

instance (Show a) => Show (PowerSeries a) where
    show ps = show_ 0 ps
      where
        show_ n Empty = "_" ++ show n
        show_ n (h :& Empty) = "(" ++ show h ++ ")_" ++ show n
        show_ n (h :& ps) = "(" ++ show h ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) ps

instance (Semigroup a) => Semigroup (PowerSeries a) where
    Empty <> ps = ps
    ps <> Empty = ps
    (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) :& (ps1 <> ps2)

instance (Monoid a) => Monoid (PowerSeries a) where
    mempty = Empty

instance (Group a) => Group (PowerSeries a) where
    invert Empty = Empty
    invert (h :& ps) = (invert h) :& (invert ps)

--------------- Algebra ----------------

type Algebra sc b = Sum sc (Product b)

instance (Scalar sc, Eq b) => Num (Algebra sc b) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = (term (fromInteger n) One) +: Zero

    abs = error "abs not implemented for Algebra"

    signum = error "signum not implemented for Algebra"

--------------- Algebra2 ----------------

type Algebra2 sc b = Sum sc (Product b, Product b)

instance (Scalar sc, Eq b) => Num (Algebra2 sc b) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = (term (fromInteger n) (One, One)) +: Zero

    abs = error "abs not implemented for Algebra2"

    signum = error "signum not implemented for Algebra2"

type GradedAlgebra sc b = PowerSeries (Algebra sc b)

type GradedAlgebra2 sc b = PowerSeries (Algebra2 sc b)

instance (Scalar sc, Eq b) => Num (GradedAlgebra sc b) where
    (+) = (<>)

    negate = invert

    a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListPS a, toListPS b]

    fromInteger n = (fromInteger n) :& Empty

    abs = error "abs not implemented for GradedAlgebra"

    signum = error "signum not implemented for GradedAlgebra"

instance (Scalar sc, Eq b) => Num (GradedAlgebra2 sc b) where
    (+) = (<>)

    negate = invert

    a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
      where
        ab_list = [toListPS a, toListPS b]

    fromInteger n = (fromInteger n) :& Empty

    abs = error "abs not implemented for GradedAlgebra2"

    signum = error "signum not implemented for GradedAlgebra2"
