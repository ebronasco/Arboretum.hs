{-# LANGUAGE TypeOperators, ExplicitNamespaces #-}

module VectorSpace (
  Sum(..),
  Product(..),
) where

data Sum k a = (k, a) :+ (Sum k a) | (k, a) :+: (k, a) | Zero

data Product a = a :* (Product a) | a :*: a | One

infixr 7 :+
infixr 7 :+:

infixr 8 :*
infixr 8 :*:

instance (Show k, Show a) => Show (Sum k a) where
  show ((k, a) :+ b) = show k ++ " *^ " ++ show a ++ " + " ++ show b
  show ((k, a) :+: (k', a')) = show k ++ " *^ " ++ show a ++ " + " ++ show k' ++ " *^ " ++ show a'
  show Zero = "0"

instance Show a => Show (Product a) where
  show (a :* b) = show a ++ " * " ++ show b
  show (a :*: a') = show a ++ " * " ++ show a'
  show One = "1"
