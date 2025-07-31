{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import AromaticTree
import Control.Monad.State.Lazy
import Data.Group
import qualified Data.List as L
import Data.Monoid as M
import qualified Data.MultiSet as MS
import Debug.Trace
import GradedList
import Graph
import Numeric.LinearAlgebra as LA
import Output
import RootedTree
import Symbolics as S
import SyntacticTree

-- Using Graph.hs

buildGraphs = do
    v <- getVertex
    u <- getVertex
    let g1 = integerGraph [v, u] [(u, v)]
    let rg1 = rooted g1 v

    v <- getVertex
    u <- getVertex
    let g2 = integerGraph [v, u] [(u, u)]

    return (rg1, g1, g2)

(rg1, g1, g2) = evalState buildGraphs [1 ..]

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
    => S.Vector (S.VectorScalar t) [t]
    -> S.Vector (S.VectorScalar t) [t]
    -> S.Vector (S.VectorScalar t) [t]
expGL gen start = S.vectorFromNonDecList
                    $ foldr1 (++)
                    $ map (terms . (\(k,x) -> S.scale (1 / (fromInteger $ product [1..k])) x))
                    $ zip (1:[1..] :: [Integer])
                    $ iterate (S.bilinear gl gen) start

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
    => S.Vector (S.VectorScalar t) [t]
    -> ([t] -> S.VectorScalar t)
    -> S.Vector (S.VectorScalar t) [t]
bseries gen coeff = S.renormalize (\_ x -> coeff x) $ expGL gen $ S.vector []

-- RK coeffs

v1 = LA.vector $ take 4 [1, 1 ..]

-- RK4
b = LA.vector [1 / 8, 3 / 8, 3 / 8, 1 / 8]

a = LA.matrix 4 [0, 0, 0, 0, 1 / 3, 0, 0, 0, -1 / 3, 1, 0, 0, 1, -1, 1, 0]

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
    => S.Vector (S.VectorScalar t) [t]
    -> LA.Matrix LA.R
    -> LA.Vector LA.R
    -> S.Vector (S.VectorScalar t) [t]
rkbseries gen aij bi = renormalize factorize $ bseries gen $ product . map (rkCoeff aij bi)
  where
    factorize k ts = k * (factorize' ts)
    factorize' ts = (1 / (factorial $ length ts)) * (product $ map (factorize' . children) ts)
    factorial n = fromInteger $ toInteger $ product [1..n]

exact = expGL (S.vector [PT 1 []]) $ S.vector [] :: S.Vector LA.R [PlanarTree Integer]
rk = rkbseries (S.vector [PT 1 []]) a b
err = S.takeV 10 $ rk - exact

-- DEBUG

vectorFNDL x = vectorFromNonDecList $ trace ("x: " ++ (show $ take 3 x)) x

willHang x y =
    vectorFromNonDecList $
        (terms y) `conc` (terms $ willHang x $ x * y)

wontHang x y = [y] `conc` (wontHang x $ x `conc` y)

conc = (++)

infvec = vectorFromNonDecList [i *^ (take i $ repeat 'c') | i <- [0 ..]]

-- / DEBUG

main = do
    putStrLn "Graph 1"
    print g1
    putStrLn "Rooted Graph 1"
    print rg1
    putStrLn "Graph 2"
    print g2
