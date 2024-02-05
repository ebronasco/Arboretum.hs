{-# LANGUAGE PatternSynonyms #-}

module SymLists (
--     Sum (Zero),
--     pattern (:+),
--     (+:),
--     PowerSeries (..),
) where

import Data.Group
import GradedList

--------------- Product ----------------
--
-- data Product b = b :* (Product b) | One deriving (Eq)
-- 
-- infixr 7 :*
-- 
-- instance Graded b => Graded (Product b) where
--     grading One = 0
--     grading (t :* p) = grading t + grading p
-- 
-- instance (Show b) => Show (Product b) where
--     show One = "1"
--     show (t :* One) = show t
--     show (t :* p) = show t ++ " * " ++ show p
-- 
-- instance Semigroup (Product b) where
--     One <> p = p
--     p <> One = p
--     (t :* p1) <> p2 = t :* (p1 <> p2)
-- 
-- instance Monoid (Product b) where
--     mempty = One
-- 
--
--
--------------- Algebra2 ----------------
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
-- type GradedAlgebra2 sc b = PowerSeries (Algebra2 sc b)
-- 
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
