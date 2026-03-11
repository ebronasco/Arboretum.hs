{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  Shuffle-Deconcatenation Hopf algebra is the dual of the
--  Concatenate-Deshuffle Hopg algebra.
--
-- This example is almost identical to the Concatenate-Deshuffle example, please see
-- the Concatenate-Deshuffle example first as we do not comment on the code that is
-- repeated.

import Core.Algebra (
    antipode,
    deconcatenate,
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

instance IsVector Char where
    type VectorScalar Char = Integer
    type VectorBasis Char = Char
    vector = vector . (1 *^)

type HopfAlgebra = Vector Integer String

type HopfAlgebra2 = Vector Integer (String, String)

-- | Algebra structure
unit :: HopfAlgebra
unit = vector []

{- |
  We do not use the default concatenate monoid structure on strings to
  obtain the algebra structure. Instead, we use the shuffle product.
-}
prod' :: HopfAlgebra -> HopfAlgebra -> HopfAlgebra
prod' = bilinear shuffle

prod :: HopfAlgebra2 -> HopfAlgebra
prod = linear (uncurry shuffle)

-- | Coalgebra structure
counit' :: String -> Integer
counit' [] = 1
counit' _ = 0

counit :: HopfAlgebra -> Integer
counit = functional counit'

-- | We use deconcatenation coproduct instead of deshuffle coproduct.
coprod :: HopfAlgebra -> HopfAlgebra2
coprod = linear deconcatenate

-- | Convolution product
convProd
    :: (HopfAlgebra -> HopfAlgebra)
    -> (HopfAlgebra -> HopfAlgebra)
    -> (HopfAlgebra -> HopfAlgebra)
convProd f1 f2 =
    prod
        . linear2 (f1 . vector, f2 . vector)
        . coprod

-- | Antipode
ant :: HopfAlgebra -> HopfAlgebra
ant = linear antipode

main :: IO ()
main = do
    let v1 = vector "abc"
    let v2 = vector "xyz"

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
