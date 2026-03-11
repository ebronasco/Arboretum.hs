{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- \|
--  In this example, we build some arbitrary graphs and perform a grafting operation on them.
--
--  We use @getVertex@ to get unique vertices for our graphs. We build two graphs, one of
--  which is rooted. Finally, we graft the rooted graph onto the other graph.

import Butcher.Graph (
    IntegerGraph,
    Rooted,
    getVertex,
    graftGraph,
    integerGraph,
    rooted,
 )
import Control.Monad.State.Lazy
import Core.Output (
    waitForEnter,
 )

buildGraphs :: State [Integer] (Rooted IntegerGraph, IntegerGraph, IntegerGraph)
buildGraphs = do
    v <- getVertex
    u <- getVertex
    let g1 = integerGraph [v, u] [(u, v)]
    let rg1 = rooted g1 v

    x <- getVertex
    y <- getVertex
    let g2 = integerGraph [x, y] [(y, y)]

    return (rg1, g1, g2)

main :: IO ()
main = do
    let (rg1, g1, g2) = evalState buildGraphs [1 ..]

    putStrLn "Graph 1"
    print g1
    waitForEnter

    putStrLn "Rooted Graph 1"
    print rg1
    waitForEnter

    putStrLn "Graph 2"
    print g2
    waitForEnter

    putStrLn "Graft Graph 1 onto Graph 2"
    print $ graftGraph rg1 g2
