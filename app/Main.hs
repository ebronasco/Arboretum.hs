{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import Control.Monad.State.Lazy
import Data.MultiSet as MS

import Core.GradedList
import Core.Output
import Core.SyntacticTree
import Core.VectorSpace
import Core.Algebra
import Butcher.Aromatic
import Butcher.Graph
import Butcher.NonPlanar
import Butcher.Planar
import Butcher.Series

-- Example: Using Graph.hs

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


main = do
    putStrLn "Graph 1"
    print g1
    putStrLn "Rooted Graph 1"
    print rg1
    putStrLn "Graph 2"
    print g2
