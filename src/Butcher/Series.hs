{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : ButcherSeries
Description : (EXPERIMENTAL) Butcher and Lie-Butcher series over classical, decorated, and aromatic forests
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

(EXPERIMENTAL) Implementation of Butcher and Lie-Butcher series over classical, decorated, and aromatic forests
-}
module Butcher.Series (
    expGL,
    bSeries,
    lbSeries,
    rkCoeff,
    rkBSeries,
) where

import Butcher.Tree
import Core.GradedList
import Core.VectorSpace
import qualified Data.MultiSet as MS
import qualified Numeric.LinearAlgebra as LA

{- |
  Consider an ODE $dy/dt = f(y)$ and let $f(y)$ be expressed using a linear combination of
  trees $v$. Let $\phi \circ y$ be the exact solution composed with a test function $\phi$,
  then,
  \[ \phi \circ y = \exp^{GL} (v) [\phi] , \]
  where $\exp^{GL}$ is the Grossman-Larson exponential and the square brackets denote the
  application of the corresponding differential operator to the test function $\phi$.

  The function @expGL@ implements the exponential $\exp^{GL}$.
-}
expGL
    :: ( IsTree t
       , IsVector t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , Fractional (VectorScalar t)
       )
    => Vector (VectorScalar t) [t]
    -> Vector (VectorScalar t) [t]
    -> Vector (VectorScalar t) [t]
expGL gen start =
    vectorFromNonDecList $
        foldr1 (++) $
            map (terms . (\(k, x) -> scale (factDiv k) x)) $
                zip (1 : [1 ..] :: [Integer]) $
                    iterate (bilinear grossmanLarson gen) start
  where
    factDiv k = 1 / fromInteger (product [1 .. k])

{- |
  Construct a Lie-Butcher series over ordered forests. The function @lbSeries@ takes a
  non-decreasing list of forests and a function that assigns a coefficient to each forest,
  and returns the corresponding Lie-Butcher series as a vector.
-}
lbSeries
    :: ( IsTree t
       , IsVector t
       , Eq (Decoration t)
       , Graded (Decoration t)
       )
    => [[t]]
    -> ([t] -> VectorScalar t)
    -> Vector (VectorScalar t) [t]
lbSeries forests coeff = vectorFromNonDecList $ map (\f -> coeff f *^ f) forests

{- |
  Construct a Butcher series over non-ordered forests. The function @bSeries@ takes a
  non-decreasing list of forests and a function that assigns a coefficient to each forest,
  and returns the corresponding Butcher series as a vector.
-}
bSeries
    :: ( IsTree t
       , IsVector t
       , Eq (Decoration t)
       , Graded (Decoration t)
       )
    => [MS.MultiSet t]
    -> (MS.MultiSet t -> VectorScalar t)
    -> Vector (VectorScalar t) (MS.MultiSet t)
bSeries forests coeff = vectorFromNonDecList $ map (\f -> coeff f *^ f) forests

---------------------------------------------------------------------

-- * Runge-Kutta methods and B-series

---------------------------------------------------------------------

{- |
  Compute the Runge-Kutta coefficient for a given tree. The function @rkCoeff@
  takes the number of stages @s@, the matrix of coefficients @aij@,
  the vector of weights @bi@, and a tree @t@, and returns the corresponding
  Runge-Kutta coefficient as a real number.
-}
rkCoeff
    :: (IsTree t)
    => Int
    -> LA.Matrix LA.R
    -> LA.Vector LA.R
    -> t
    -> LA.R
rkCoeff s aij bi t = (LA.<.>) bi $ product $ (v1s :) $ map rkInternalCoeff $ branches t
  where
    rkInternalCoeff t' = (LA.#>) aij $ product $ (v1s :) $ map rkInternalCoeff $ branches t'
    v1s = LA.vector $ take s [1, 1 ..]

{- |
  Construct a Butcher series over non-ordered forests listed in @forests@
  of a Runge-Kutta method with @s@ stages and coefficients @bi@ and @aij@.
-}
rkBSeries
    :: ( IsTree t
       , IsVector t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , VectorScalar t ~ LA.R
       , Fractional (VectorScalar t)
       )
    => [MS.MultiSet t]
    -> Int
    -> LA.Matrix LA.R
    -> LA.Vector LA.R
    -> Vector (VectorScalar t) (MS.MultiSet t)
rkBSeries forests s aij bi = bSeries forests $ product . MS.map (rkCoeff s aij bi)
