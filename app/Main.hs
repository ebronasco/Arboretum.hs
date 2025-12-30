{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import Control.Monad.State.Lazy
import Data.Group
import Debug.Trace
import Data.Monoid as M
import qualified Data.List as L
import qualified Data.MultiSet as MS

import Core.GradedList
import Core.Output
import Core.SyntacticTree
import Core.VectorSpace as V
import Core.Algebra
import Butcher.Aromatic
import Butcher.Graph
import Butcher.NonPlanar
import Butcher.Planar
import Butcher.Series

import Numeric.LinearAlgebra as LA

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



-- DEBUG

a' :: Integer -> PlanarTree Integer -> Double
a' _ (PT 1 []) = 2.0
a' _ (PT 1 [PT 1 []]) = 3.0
a' _ (PT 1 [PT 1 [PT 1 []]]) = 5.0
a' _ (PT 1 [PT 1 [], PT 1 []]) = 7.0


-- RK coeffs

v1 = LA.vector $ take 4 [1, 1 ..]

-- RK4
b = LA.vector [1 / 8, 3 / 8, 3 / 8, 1 / 8]

a = LA.matrix 4 [0, 0, 0, 0, 1 / 3, 0, 0, 0, -1 / 3, 1, 0, 0, 1, -1, 1, 0]



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
