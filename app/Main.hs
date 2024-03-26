{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TupleSections #-}

import GradedList
import Graph
import Symbolics
import Output
import RootedTree
import AromaticTree
import Substitution

import qualified Data.MultiSet as MS
import qualified Data.List as L
import Data.Group
import Control.Monad.State.Lazy

 -- Using Graph.hs

buildGraphs = do
    v <- getVertex
    u <- getVertex
    let g1 = integerGraph [v,u] [(u,v)]
    let rg1 = rooted g1 v

    v <- getVertex
    u <- getVertex
    let g2 = integerGraph [v,u] [(u,u)]

    return (rg1, g1, g2)

(rg1, g1, g2) = evalState buildGraphs [1 ..]


 -- Using RootedTree.hs

t1 = PRTree 0 [PRTree 0 []]

f2 = [PRTree 0 [], PRTree 0 []]



main = putStrLn "Hello, world!"
