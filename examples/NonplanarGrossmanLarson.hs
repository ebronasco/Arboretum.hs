{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  In this example, we build the Gorssman-Larson Hopf algebra
--  over nonplanar rooted forests.
--
--  Many parts of this example are similar to the ConcatDeshuffle example and these
--  parts will not be explained in detail. The main difference is that the basis elements of
--  characters is replaced by the basis elements of nonplanar rooted trees with the
--  multiset of trees denoting a forest.
--
--  The algebra structure is given by the Grossman-Larson product and the coalgebra structure is
--  given by the deshuffle coproduct. The antipode is obtained using the recursive formula for an
--  antipode of a graded connected bialgebra.

import Butcher.NonPlanar (
    Tree,
 )
import Butcher.Tree (
    fromBrackets,
    grossmanLarson,
 )
import Core.Algebra (
    antipodeWith,
    deshuffle,
 )
import Core.Output (
    display,
    displayShow,
    waitForEnter,
 )
import Core.VectorSpace (
    IsVector (..),
    Vector,
    bilinear,
    functional,
    linear,
    linear2,
    rescale,
    vector,
    (*^),
 )
import Data.MultiSet as MS (
    MultiSet,
    empty,
    null,
 )

instance IsVector (Tree Integer) where
    type VectorScalar (Tree Integer) = Integer
    type VectorBasis (Tree Integer) = Tree Integer
    vector = vector . (1 *^)

type HopfAlgebra = Vector Integer (MultiSet (Tree Integer))

type HopfAlgebra2 = Vector Integer (MultiSet (Tree Integer), MultiSet (Tree Integer))

-- | Algebra structure
unit :: HopfAlgebra
unit = vector empty

prod' :: HopfAlgebra -> HopfAlgebra -> HopfAlgebra
prod' = bilinear grossmanLarson

prod :: HopfAlgebra2 -> HopfAlgebra
prod = linear (uncurry grossmanLarson)

-- | Coalgebra structure
counit' :: MultiSet (Tree Integer) -> Integer
counit' ms
    | MS.null ms = 1
    | otherwise = 0

counit :: HopfAlgebra -> Integer
counit = functional counit'

coprod :: HopfAlgebra -> HopfAlgebra2
coprod = linear deshuffle

-- | Convolution product
convProd
    :: (HopfAlgebra -> HopfAlgebra)
    -> (HopfAlgebra -> HopfAlgebra)
    -> (HopfAlgebra -> HopfAlgebra)
convProd f1 f2 =
    prod
        . linear2 (f1 . vector, f2 . vector)
        . coprod

{- |
  Obtain antipode from the given unit, product, and coproduct using
  the recursive formula for an antipode of a graded connected bialgebra.
-}
ant :: HopfAlgebra -> HopfAlgebra
ant = linear $ antipodeWith empty grossmanLarson deshuffle

main :: IO ()
main = do
    let v1 = vector (fromBrackets "1[2],3" :: MultiSet (Tree Integer))
    let v2 = vector (fromBrackets "4[5]" :: MultiSet (Tree Integer))

    putStrLn "Product of a unit and a vector."
    display $ prod' unit v1
    waitForEnter

    putStrLn "Product of two vectors."
    display $ prod' v1 v2
    waitForEnter

    putStrLn "Counit of a vector."
    displayShow $ counit v1
    waitForEnter

    putStrLn "Coproduct of a vector."
    display $ coprod v1
    waitForEnter

    putStrLn "Checking the counit property: $(id \\otimes counit) \\circ coproduct = id$."
    display $ rescale (counit' . snd) $ coprod v2
    waitForEnter

    putStrLn "Compute the antipode of a vector."
    display $ ant v1
    waitForEnter

    putStrLn "Check the antipode property: $prod \\circ (id \\otimes antipode) \\circ coprod = unit \\circ counit$."
    display $ convProd id ant v1
