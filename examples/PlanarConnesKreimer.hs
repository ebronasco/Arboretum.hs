{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  In this example, we build the Connes-Kreimer Hopf algebra
--  over planar rooted forests.
--
--  Many parts of this example are similar to the ConcatDeshuffle example and these
--  parts will not be explained in detail. The main difference is that the basis elements of
--  characters is replaced by the basis elements of planar rooted trees with the list of trees
--  denoting a forest.
--
--  The algebra structure is given by shuffle product and the coalgebra structure is
--  given by the Connes-Kreimer coproduct. The antipode is obtained using the recursive formula
--  for an antipode of a graded connected bialgebra.

import Butcher.Planar (
    PlanarTree,
 )
import Butcher.Tree (
    connesKreimer,
    fromBrackets,
 )
import Core.Algebra (
    antipodeWith,
    shuffle,
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

instance IsVector (PlanarTree Integer) where
    type VectorScalar (PlanarTree Integer) = Integer
    type VectorBasis (PlanarTree Integer) = PlanarTree Integer
    vector = vector . (1 *^)

type HopfAlgebra = Vector Integer [PlanarTree Integer]

type HopfAlgebra2 = Vector Integer ([PlanarTree Integer], [PlanarTree Integer])

-- | Algebra structure
unit :: HopfAlgebra
unit = vector []

{- |
  We do not use the default concatenate monoid structure on lists to
  obtain the algebra structure. Instead, we use the shuffle product.
-}
prod' :: HopfAlgebra -> HopfAlgebra -> HopfAlgebra
prod' = bilinear shuffle

prod :: HopfAlgebra2 -> HopfAlgebra
prod = linear (uncurry shuffle)

-- | Coalgebra structure
counit' :: [PlanarTree Integer] -> Integer
counit' [] = 1
counit' _ = 0

counit :: HopfAlgebra -> Integer
counit = functional counit'

coprod :: HopfAlgebra -> HopfAlgebra2
coprod = linear connesKreimer

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
ant = linear $ antipodeWith [] shuffle connesKreimer

main :: IO ()
main = do
    let v1 = vector (fromBrackets "1[2],3" :: [PlanarTree Integer])
    let v2 = vector (fromBrackets "4[5]" :: [PlanarTree Integer])

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
