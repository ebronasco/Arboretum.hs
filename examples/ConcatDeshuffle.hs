{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  Concatenation-Deshuffle Hopf algebra is one of the most common examples
--  of a combinatorial Hopf algebra.
--
--  In this example, we build the Hopf algebra using strings (lists of
--  characters) with the scalars given by integers.

import Core.Algebra (
    antipode,
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
    functional,
    linear,
    linear2,
    rescale,
    vector,
    (*^),
 )

{- |
  Define @Char@ to be elements of a vector space spanned by @Char@ over integers.
  Strings, which are lists of @Char@, are automaticcally recongnized as elements
  of a vector space spanned by strings over integers. Since strings can be
  concatenated, they form a monoid under concatenation. Consequently, the vector
  space spanned by strings carries a natural algebra structure.

  In Haskell terms, this means that there is an instance of @Num String@,
  allowing vectors to be added and multiplied using @(+)@ and @(*)@.
-}
instance IsVector Char where
    type VectorScalar Char = Integer
    type VectorBasis Char = Char

    -- \| Always use this definition of @vector@ unless you know what you are doing.
    vector = vector . (1 *^)

{- |
  Hopf algebra is a vector space spanned by strings over the integer scalars together
  with a compatible algebra, coalgebra structures, and an antipode.
-}
type HopfAlgebra = Vector Integer String

-- | Tensor product of HopfAlgebra with itself.
type HopfAlgebra2 = Vector Integer (String, String)

-- | Algebra structure
unit :: HopfAlgebra
unit = vector []

{- |
  We have the product @(*) :: HopfAlgebra -> HopfAlgebra -> HopfAlgebra@ from the @Num@
  instance of @String@. However, the product is often used in as a part of a formula which
  usually assumes it to have the type signature @HopfAlgebra2 -> HopfAlgebra@. Therefore,
  we define @prod@.
-}
prod :: HopfAlgebra2 -> HopfAlgebra
prod = linear (uncurry (++))

-- | Coalgebra structure
counit' :: String -> Integer
counit' [] = 1
counit' _ = 0

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

-- | Antipode
ant :: HopfAlgebra -> HopfAlgebra
ant = linear antipode

main :: IO ()
main = do
    let v1 = vector "abc"
    let v2 = vector "xyz"

    putStrLn "Product of a unit and a vector."
    display $ unit * v1
    waitForEnter

    putStrLn "Product of two vectors."
    display $ v1 * v2
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
