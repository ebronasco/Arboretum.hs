{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import AromaticTree
import Control.Monad.State.Lazy
import Data.Group
import qualified Data.List as L
import qualified Data.MultiSet as MS
import GradedList
import Graph
import Output
import RootedTree
import SyntacticTree
import Symbolics

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

-- Using RootedTree.hs

t1 = PT 1 [PT 1 []]

f2 = [PT 1 [], PT 1 [PT 1 [], PT 1 []]]

{-
   display $ vector t1
   display $ vector f2
   display $ [t1] `graftFF` f2
   display $ linear nonplanarF $ [t1] `graftFF` f2
-}

-- Using AromaticTree.hs
{-
paf1 =
    ( [planarAroma [PT 1 [], PT 1 []], planarAroma [PT 1 []], planarAroma [PT 1 []]]
    , [PT 1 [PT 1 [], PT 1 []]]
    )
        :: AromaticPlanarForest Integer

paf2 =
    ( [planarAroma [PT 1 []]]
    , [PT 1 []]
    )
        :: AromaticPlanarForest Integer
-}
{-
   display $ vector paf1
   display $ vector paf2
   display $ paf2 `graftAF` paf1
   display $ linear nonplanarAF $ paf2 `graftAF` paf1
-}
{-
pat1 =
    ( [planarAroma [PT 1 [], PT 1 []], planarAroma [PT 1 []], planarAroma [PT 1 []]]
    , PT 1 [PT 1 [], PT 1 []]
    )
        :: AromaticPlanarTree Integer
-}
{-
   display $ vector pat1
   display $ divergenceAT pat1
   display $ linear nonplanarA $ divergenceAT pat1
-}

-- Using Substitution.hs

pt0 = PT 1 [PT 1 [PT 1 [], PT 1 []], PT 2 []]
pt1 = PT 1 [PT 1 []]
pt2 = PT 1 [PT 1 [], PT 1 []]

{-
   display $ vector [pt0]
   display $ toOperad pt0

   display $ vector [pt1]
   display $ substitute [pt1, pt1, pt1, pt1, pt1] pt0

   display $ vector [pt2]
   display $ toOperad pt2
   display $ substitute [pt1, PT 1 [], PT 1 []] pt2
-}
{-
at1 = ([planarAroma [PT 1 []]], PT 2 [])
at2 = ([], PT 1 [PT 2 []])
at3 = ([planarAroma [PT 1 [], PT 1 []]], PT 1 [])
af1 = ([planarAroma [PT 3 []]], [PT 3 [PT 4 []]])
af2 = ([planarAroma [PT 3 [PT 5 []], PT 3 []]], [PT 3 [PT 4 []]])
-}
{-
    display $ substitute 3 [at2, at2] af1
    display $ substitute 3 [at1, at1] af1
-}

main = putStrLn "Hello, world!"
