{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module SymLists (
    Basis,
    Product (One),
    Sum (Zero),
--    leadingCoeff,
--    leadingElement,
--    PowerSeries (..),
--    Algebra,
--    Algebra2,
--    GradedAlgebra,
--    GradedAlgebra2,
) where

import Data.Group
import GradedList

data Basis b = Basis {unBasis :: b} deriving (Eq)

basis :: b -> Basis b
basis = Basis

instance (Show b) => Show (Basis b) where
    show = show . unBasis

--------------- Product ----------------

data Product b = b :* (Product b) | One deriving (Eq)

infixr 7 :*

instance Graded b => Graded (Product b) where
    grading One = 0
    grading (t :* p) = grading t + grading p

instance (Show b) => Show (Product b) where
    show One = "1"
    show (t :* One) = show t
    show (t :* p) = show t ++ " * " ++ show p

instance Semigroup (Product b) where
    One <> p = p
    p <> One = p
    (t :* p1) <> p2 = t :* (p1 <> p2)

instance Monoid (Product b) where
    mempty = One

class IsProduct p where
    type ProductBasis p 
    toProduct :: p -> Product (ProductBasis p)

instance IsProduct (Basis b) where
    type ProductBasis (Basis b) = b
    toProduct (Basis b) = b :* One

instance IsProduct (Product b) where
    type ProductBasis (Product b) = b
    toProduct = id

--------------- Term (internal) ----------------

data Term k b = k :*^ (Product b) deriving (Eq)

getScalar :: Term k b -> k
getScalar (k :*^ _) = k

getBasis :: Term k b -> Product b
getBasis (_ :*^ b) = b

(*^) :: (ProductBasis p ~ b, IsProduct p) => k -> p -> Term k b
k *^ p = k :*^ (toProduct p)

instance (Show k, Show b) => Show (Term k b) where
    show (k :*^ b) = show k ++ " *^ " ++ show b

-- Choose the Product monoid of Num for the scalars.
instance (Num k, Semigroup b) => Semigroup (Term k b) where
    (k1 :*^ b1) <> (k2 :*^ b2) = (k1 * k2) *^ (b1 <> b2)

instance (Num k, Semigroup b) => Monoid (Term k b) where
    mempty = (fromInteger 1) *^ One

--------------- Sum ----------------

pattern (:+) :: Term sc b -> Sum sc b -> Sum sc b
pattern t :+ s <- Sum t s

data Sum k b = Sum (Term k b) (Sum k b) | Zero

fromListS :: (Num k, Eq k, Eq b) => [Term k b] -> Sum k b
fromListS [] = Zero
fromListS (h : t) = h +: fromListS t

toListS :: Sum k b -> [Term k b]
toListS Zero = []
toListS (h :+ s) = h : toListS s

instance (Show k, Show b) => Show (Sum k b) where
    show ((k :*^ b) :+ Zero) = show k ++ " *^ " ++ show b
    show ((k :*^ b) :+ s) = show k ++ " *^ " ++ show b ++ " + " ++ show s
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
(+:) :: (Num k, Eq k, Eq b) => Term k b -> Sum k b -> Sum k b
(+:) (0 :*^ _) s = s
(+:) t s = case maybeAddTerm t s of
    Nothing -> Sum t s
    Just s' -> s'
  where
    maybeAddTerm t1 Zero = Nothing
    maybeAddTerm t1 (t2 :+ s2) =
        if t1_basis == (getBasis t2)
            then
                if scalar_sum /= 0
                    then Just $ Sum (scalar_sum *^ t1_basis) s2
                    else Just s2
            else case maybeAddTerm t1 s2 of
                Nothing -> Nothing
                Just s2' -> Just $ Sum t2 s2'
      where
        t1_basis = getBasis t1
        scalar_sum = (getScalar t1) + (getScalar t2)

instance (Num k, Eq k, Eq b) => Semigroup (Sum k b) where
    Zero <> s2 = s2
    s1 <> Zero = s1
    (t :+ s1) <> s2 = t +: (s1 <> s2)

instance (Num k, Eq k, Eq b) => Monoid (Sum k b) where
    mempty = Zero

instance (Num k, Eq k, Eq b) => Group (Sum k b) where
    invert Zero = Zero
    invert (t :+ s) = ((negate $ getScalar t) *^ (getBasis t)) +: (invert s)

instance (Num k, Eq k, Eq b) => Eq (Sum k b) where
    s1 == s2 = (s1 <> (invert s2)) == Zero

instance (Num k, Eq k, Eq b, Semigroup b) => Num (Sum k b) where
    (+) = (<>)

    negate = invert

    a * b = fromListS $ map mconcat $ distributeLists ab_list
      where
        ab_list = [toListS a, toListS b]

    fromInteger n = ((fromInteger n) *^ One) +: Zero

    abs = error "abs not implemented for Algebra"

    signum = error "signum not implemented for Algebra"

class IsSum s where
    type SumScalar s
    type SumBasis s
    toSum :: s -> Sum (SumScalar s) (SumBasis s)

instance (Num k, Eq k, Eq b) => IsSum (Term k b) where
    type SumBasis (Term k b) = b
    type SumScalar (Term k b) = k
    toSum = (+: Zero)

instance (Num k, Eq k, Eq b, IsProduct p, ProductBasis p ~ b) => IsSum p where
    type SumBasis p = ProductBasis p
    type SumScalar p = Integer
    toSum p = toSum $ (fromInteger 1) *^ (toProduct p)



-- --------------- PowerSeries ----------------
-- 
-- infixr 6 :&
-- 
-- data PowerSeries a = a :& (PowerSeries a) | Empty deriving (Eq)
-- 
-- fromListPS :: [a] -> PowerSeries a
-- fromListPS [] = Empty
-- fromListPS (h : t) = h :& fromListPS t
-- 
-- toListPS :: PowerSeries a -> [a]
-- toListPS Empty = []
-- toListPS (h :& ps) = h : toListPS ps
-- 
-- instance (Show a) => Show (PowerSeries a) where
--     show ps = show_ 0 ps
--       where
--         show_ n Empty = "_" ++ show n
--         show_ n (h :& Empty) = "(" ++ show h ++ ")_" ++ show n
--         show_ n (h :& ps) = "(" ++ show h ++ ")_" ++ show n ++ " + " ++ show_ (n + 1) ps
-- 
-- instance (Semigroup a) => Semigroup (PowerSeries a) where
--     Empty <> ps = ps
--     ps <> Empty = ps
--     (h1 :& ps1) <> (h2 :& ps2) = (h1 <> h2) :& (ps1 <> ps2)
-- 
-- instance (Monoid a) => Monoid (PowerSeries a) where
--     mempty = Empty
-- 
-- instance (Group a) => Group (PowerSeries a) where
--     invert Empty = Empty
--     invert (h :& ps) = (invert h) :& (invert ps)
-- 
-- --------------- Algebra2 ----------------
-- 
-- type Algebra2 sc b = Sum sc (Product b, Product b)
-- 
-- instance (Scalar sc, Eq b) => Num (Algebra2 sc b) where
--     (+) = (<>)
-- 
--     negate = invert
-- 
--     a * b = fromListS $ map mconcat $ distributeLists ab_list
--       where
--         ab_list = [toListS a, toListS b]
-- 
--     fromInteger n = (term (fromInteger n) (One, One)) +: Zero
-- 
--     abs = error "abs not implemented for Algebra2"
-- 
--     signum = error "signum not implemented for Algebra2"
-- 
-- type GradedAlgebra sc b = PowerSeries (Algebra sc b)
-- 
-- type GradedAlgebra2 sc b = PowerSeries (Algebra2 sc b)
-- 
-- instance (Scalar sc, Eq b) => Num (GradedAlgebra sc b) where
--     (+) = (<>)
-- 
--     negate = invert
-- 
--     a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
--       where
--         ab_list = [toListPS a, toListPS b]
-- 
--     fromInteger n = (fromInteger n) :& Empty
-- 
--     abs = error "abs not implemented for GradedAlgebra"
-- 
--     signum = error "signum not implemented for GradedAlgebra"
-- 
-- instance (Scalar sc, Eq b) => Num (GradedAlgebra2 sc b) where
--     (+) = (<>)
-- 
--     negate = invert
-- 
--     a * b = fromListPS $ map sum $ map (map product) $ distributeGradedLists ab_list
--       where
--         ab_list = [toListPS a, toListPS b]
-- 
--     fromInteger n = (fromInteger n) :& Empty
-- 
--     abs = error "abs not implemented for GradedAlgebra2"
-- 
--     signum = error "signum not implemented for GradedAlgebra2"
