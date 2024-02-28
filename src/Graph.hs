{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Graph (
    GraphEdge,
    EndPoint,
    edge,
    source,
    target,
    Graph,
    Vertex,
    Edge,
    singleton,
    edges,
    vertices,
    addGraph,
    addEdge,
    IntegerGraph,
    integerGraph,
    RootedGraph,
    root,
    Rooted,
    rooted,
    graft,
    graftTo,
    uniqueVertex,
    rootedTreeGraph,
) where

import qualified Data.List as L (
    init,
 )
import qualified Data.MultiSet as MS (
    MultiSet,
    empty,
    fromList,
    insert,
    singleton,
    toList,
    union,
 )

import Control.Monad.State

import Symbolics
import qualified RootedTree as RT

import GradedList (
    Graded,
    grading,
 )


class GraphEdge e where
    type EndPoint e
    edge :: a -> EndPoint e -> EndPoint e -> e
    source :: e -> EndPoint e
    target :: e -> EndPoint e

-- Integer Edge

instance GraphEdge (a, a) where
    type EndPoint (a, a) = a
    edge _ = (,)
    source (x, _) = x
    target (_, y) = y

class
    ( GraphEdge (Edge g)
    , Vertex g ~ EndPoint (Edge g)
    ) =>
    Graph g
    where
    type Edge g
    type Vertex g
    type Vertex g = EndPoint (Edge g)
    singleton :: Vertex g -> g
    edges :: g -> MS.MultiSet (Edge g)
    vertices :: g -> MS.MultiSet (Vertex g)
    addGraph :: (Graph g0, Edge g ~ Edge g0) => g0 -> g -> g
    addEdge :: Edge g -> g -> g

-- Integer Graph

data IntegerGraph
    = IG
        (MS.MultiSet Integer)
        (MS.MultiSet (Integer, Integer))

instance Show IntegerGraph where
    show g = "IntegerGraph(V=" ++ vs ++ ", E=" ++ es ++ ")"
      where
        vs = show $ MS.toList $ vertices g
        es = show $ MS.toList $ edges g

instance Graph IntegerGraph where
    type Edge IntegerGraph = (Integer, Integer)
    singleton v = IG (MS.singleton v) MS.empty
    edges (IG _ es) = es
    vertices (IG vs _) = vs
    addGraph g (IG vs es) = IG ((vertices g) `MS.union` vs) ((edges g) `MS.union` es)
    addEdge e (IG vs es) = IG vs (e `MS.insert` es)

integerGraph :: [Integer] -> [(Integer, Integer)] -> IntegerGraph
integerGraph vs es = IG (MS.fromList vs) (MS.fromList es)

class (Graph g) => RootedGraph g where
    root :: g -> Vertex g

-- Naive Rooted Graph implementation

data Rooted g = R (Vertex g) g

instance (Show g, Show (Vertex g)) => Show (Rooted g) where
    show (R r g) = "Rooted" ++ trimmedShowG ++ ", R=" ++ (show r) ++ ")"
      where
        trimmedShowG = L.init $ show g

instance (Graph g) => Graph (Rooted g) where
    type Edge (Rooted g) = Edge g
    singleton v = R v $ singleton v
    edges (R _ g) = edges g
    vertices (R _ g) = vertices g
    addGraph g0 (R r g) = R r (addGraph g0 g)
    addEdge e (R r g) = R r (addEdge e g)

instance (Graph g) => RootedGraph (Rooted g) where
    root (R r _) = r

rooted :: g -> Vertex g -> Rooted g
rooted g r = R r g

-- Operations

instance Eq IntegerGraph where
    g1 == g2 = (vertices g1 == vertices g2) && (edges g1 == edges g2)

instance Graded IntegerGraph where
    grading = toInteger . length . vertices

instance Basis IntegerGraph

graft :: (Basis a2, RootedGraph a1, Graph a2, Edge a1 ~ Edge a2) => a1 -> a2 -> PowerSeries Integer a2
graft rg1 g2 = basisVectorG $ map (:[]) $ map (graftTo rg1 g2) $ MS.toList $ vertices g2

graftTo :: (RootedGraph a1, Graph a2, Edge a1 ~ Edge a2) => a1 -> a2 -> Vertex a2 -> a2
graftTo rg1 g2 v = addGraph rg1 $ addEdge new_edge g2
  where
    new_edge = edge () (root rg1) v

predecessors :: (Graph g) => g -> Vertex g -> [Vertex g]
predecessors g v = map source $ filter ((== v) . target) $ MS.toList $ edges g

removeVertex :: (Graph g) => g -> Vertex g -> g
removeVertex g v = foldr addEdge filteredVertices $ filter (\e -> ((source e) /= v) && ((target e) /= v)) $ MS.toList $ edges g
  where
    filteredVertices = foldr1 addGraph $ map singleton $ filter (/= v) $ MS.toList $ vertices g

rootedTreeGraph :: (RootedGraph g) => g -> RT.PRTree (Vertex g)
rootedTreeGraph g = depthFirst g (root g)
  where
    -- use state monad to store the unvisited vertices
    depthFirsts _ [] = []
    depthFirsts g0 (v:vs) = (\(tree, leftover) -> tree : depthFirsts leftover vs) $ depthFirst g0 v
    depthFirst g0 v = depthFirsts (removeVertex g0 v) $ predecessors g0 v

-- State monad

uniqueVertex :: State [a] a
uniqueVertex = state $ \l -> (head l, tail l)
