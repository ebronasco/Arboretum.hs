{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  Concatenation-Deshuffle Hopf algebra is one of the most common examples
--  of a combinatorial Hopf algebra.
--
--  In this example, we build the Hopf algebra using strings (lists of
--  characters) with the scalars given by integers.

import Butcher.Planar (
    PlanarTree,
    cosub,
 )
import Butcher.Tree (
    fromBrackets,
 )
import Core.Output (
    display,
    waitForEnter,
 )
import Core.VectorSpace (
    IsVector (..),
    linear,
    (*^),
 )

{- |
  Define @PlanarTree Integer@ to be elements of a vector space spanned by
  @PlanarTree Integer@ over integers. Forests, which are lists of
  @PlanarTree Integer@, are automaticcally recongnized as elements of a vector
  space spanned by forests over integers.
-}
instance IsVector (PlanarTree Integer) where
    type VectorScalar (PlanarTree Integer) = Integer
    type VectorBasis (PlanarTree Integer) = PlanarTree Integer

    -- \| Always use this definition of @vector@ unless you know what you are doing.
    vector = vector . (1 *^)

main :: IO ()
main = do
    -- \| Define two trees
    let t = fromBrackets "1[1,1[1]" :: [PlanarTree Integer]
    let t' = fromBrackets "1[1[1[1]" :: [PlanarTree Integer]

    -- \| Defined the vector consisting of the sum of the two trees
    let v = vector t + vector t'

    -- \| Define the infinitisimal character @a@.
    let t1 = fromBrackets "1" :: [PlanarTree Integer]
    let t2 = fromBrackets "1[1]" :: [PlanarTree Integer]
    let a _ x
            | x == t1 = 1
            | x == t2 = 2
            | otherwise = 0

    -- \| Compute the cosubstitution of a single tree.
    display $ cosub [1] a t
    waitForEnter

    -- \| Compute the cosubstitution of a vector.
    display $ linear (cosub [1] a) v
