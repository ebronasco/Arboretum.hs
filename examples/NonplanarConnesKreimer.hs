{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  In this example, we build the Connes-Kreimer Hopf algebra
--  over nonplanar rooted forests.
--
--  Many parts of this example are similar to the ConcatDeshuffle example and these
--  parts will not be explained in detail. The main difference is that the basis elements of
--  characters is replaced by the basis elements of nonplanar rooted trees with the
--  multiset of trees denoting a forest.
--
--  The algebra structure is given by the concatenation product and the coalgebra structure is
--  given by the Connes-Kreimer coproduct. The antipode is obtained using the recursive formula for an
--  antipode of a graded connected bialgebra.

import Butcher.NonPlanar (
    Tree,
 )
import Butcher.Tree (
    connesKreimer,
    fromBrackets,
 )
import Core.Algebra (
    antipodeWith,
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
import Data.MultiSet as MS (
    MultiSet,
    empty,
    null,
    union,
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

prod :: HopfAlgebra2 -> HopfAlgebra
prod = linear (uncurry union)

-- | Coalgebra structure
counit' :: MultiSet (Tree Integer) -> Integer
counit' ms
    | MS.null ms = 1
    | otherwise = 0

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

  Note that @antipodeWith@ expects the product to have signature
  @ MultiSet t -> MultiSet t -> Vector Integer (MultiSet t)@,
  so we define @prod''@.
-}
ant :: HopfAlgebra -> HopfAlgebra
ant = linear $ antipodeWith empty prod'' connesKreimer
  where
    prod'' x y = vector $ 1 *^ (x `union` y)

main :: IO ()
main = do
    let v1 = vector (fromBrackets "1[2],3" :: MultiSet (Tree Integer))
    let v2 = vector (fromBrackets "4[5]" :: MultiSet (Tree Integer))

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
