{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeOperators  #-}

{- |
Module      : ButcherSeries
Description : Butcher and Lie-Butcher series over classical, decorated, aromatic, exotic forests
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation Butcher and Lie-Butcher series over classical, decorated, aromatic, exotic forests
-}
module ButcherSeries (
    bseries,
    expGL,
    rkCoeff,
    rkbseries,
) where

import RootedTree
import Symbolics as S
import GradedList

import Numeric.LinearAlgebra as LA

bseries
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , Fractional (VectorScalar t)
       )
    => S.Vector (VectorScalar t) [t]
    -> ([t] -> VectorScalar t)
    -> S.Vector (VectorScalar t) [t]
bseries gen coeff = renormalize (\_ x -> coeff x) $ expGL gen $ S.vector []

-- Exact solution

expGL
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , Fractional (VectorScalar t)
       )
    => S.Vector (VectorScalar t) [t]
    -> S.Vector (VectorScalar t) [t]
    -> S.Vector (VectorScalar t) [t]
expGL gen start =
    vectorFromNonDecList $
        foldr1 (++) $
            map (terms . (\(k, x) -> S.scale (1 / (fromInteger $ product [1 .. k])) x)) $
                zip (1 : [1 ..] :: [Integer]) $
                    iterate (bilinear gl gen) start

-- Runge-Kutta methods



v1 :: LA.Vector LA.R
v1 = LA.vector $ take 1 [1, 1 ..]

rkCoeff
    :: (IsTree t)
    => LA.Matrix LA.R
    -> LA.Vector LA.R
    -> t
    -> LA.R
rkCoeff aij bi t = (<.>) bi $ product $ (v1 :) $ map (rkInternalCoeff aij) $ children t

rkInternalCoeff
    :: (IsTree t)
    => LA.Matrix LA.R
    -> t
    -> LA.Vector R
rkInternalCoeff aij t = (#>) aij $ product $ (v1 :) $ map (rkInternalCoeff aij) $ children t

rkbseries
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , VectorScalar t ~ LA.R
       , Fractional (VectorScalar t)
       )
    => S.Vector (VectorScalar t) [t]
    -> LA.Matrix LA.R
    -> LA.Vector LA.R
    -> S.Vector (VectorScalar t) [t]
rkbseries gen aij bi = bseries gen $ product . map (rkCoeff aij bi)


