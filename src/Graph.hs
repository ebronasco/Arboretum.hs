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
