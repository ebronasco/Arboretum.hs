{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TupleSections #-}

import GradedList
import Graph
import Symbolics

import qualified Data.MultiSet as MS
import qualified Data.List as L
import Data.Group

instance Graded Int where
  gradingFunction 0 = 0
  gradingFunction n = 1 + (grading $ n `div` 10)

[t1,t2,t10,t13,t20,t100] = map (1,) [1,2,10,13,20,100] 

v1 = vect [t13, t2, t10, t100, t1, t1, t20] :: VectorSpace (Int, Int)

v2 = vect [t13, t2, t10]

-- OPERATIONS

labeledGraftTo :: (RootedGraph g1, Graph g2, Edge g1 ~ Edge g2) => g1 -> g2 -> a -> Vertex g2 -> g2
labeledGraftTo g1 g2 a v = addEdge (edge a r v) $ addGraph g1 g2
  where
    r = root g1

graftTo :: (RootedGraph g1, Graph g2, Edge g1 ~ Edge g2) => g1 -> g2 -> Vertex g2 -> g2
graftTo g1 g2 v = labeledGraftTo g1 g2 () v

labeledGraftListTo :: (RootedGraph g1, Graph g2, Edge g1 ~ Edge g2) => [(g1, a, Vertex g2)] -> g2 -> g2
labeledGraftListTo [] g2 = g2
labeledGraftListTo ((g1, a, v) : ts) g2 = labeledGraftTo g1 (labeledGraftListTo ts g2) a v

graftListTo :: (RootedGraph g1, Graph g2, Edge g1 ~ Edge g2) => [(g1, Vertex g2)] -> g2 -> g2
graftListTo gvList g2 = labeledGraftListTo gavList g2
  where
    gavList = map (\(g, v) -> (g, (), v)) gvList

labeledAddRoot :: (RootedGraph g) => [(g, a)] -> Vertex g -> g
labeledAddRoot gaList r = labeledGraftListTo garList $ singleton r
  where
    garList = map (\(g, a) -> (g, a, r)) gaList

addRoot :: (RootedGraph g) => [g] -> Vertex g -> g
addRoot gList = labeledAddRoot gaList
  where
    gaList = map (\g -> (g, ())) gList
