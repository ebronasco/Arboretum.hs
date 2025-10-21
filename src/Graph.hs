{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Graph
Description : General graphs, rooted graphs, and grafting of graphs.
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the general Graph and RootedGraph typeclasses. As
an example, the @IntegerGraph@ type is defined as an instance of
@Graph@. The data @Rooted@ is defined as a map from @Graph@ to
@RootedGraph@. The @graftGraph@ and @graftGraphTo@ functions are also defined
here.
-}
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
    graftGraph,
    graftGraphTo,
    getVertex,
) where

import Control.Monad.State
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
import GradedList (
    Graded,
    grading,
 )
import Symbolics (
    Vector,
    vectorFromNonDecList,
    (*^),
 )

----------------------------------------------------------------------

-- * Graphs

----------------------------------------------------------------------

{- |
  To define a graph, we need to define a graph edge first. A graph
  edge must be an instance of the @GraphEdge@ typeclass.
-}
class GraphEdge e where
    {- | The @EndPoint@ type family is used to define the type of
    the vertices of the graph.
    -}
    type EndPoint e

    -- | Every edge must have a source @EndPoint@, ...
    source :: e -> EndPoint e

    -- | ... a target @EndPoint@, ...
    target :: e -> EndPoint e

    {- | ... and a way to build the edge from source, target, and
    possibly some additional information @a@.
    -}
    edge :: a -> EndPoint e -> EndPoint e -> e

-- | A naive instance of the @GraphEdge@ typeclass.
instance GraphEdge (a, a) where
    type EndPoint (a, a) = a
    edge _ = (,)
    source (x, _) = x
    target (_, y) = y

{- |
  A graph @g@ must have an instance of the @Graph@ typeclass with
  the edge type @Edge g@ being an instance of the @GraphEdge@
  typeclass and the vertex type @Vertex g@ being the @EndPoint@ of
  @Edge g@.
-}
class
    ( GraphEdge (Edge g)
    , Vertex g ~ EndPoint (Edge g)
    ) =>
    Graph g
    where
    -- | The type of the edges of the graph.
    type Edge g

    -- | The type of the vertices of the graph.
    type Vertex g

    {- | Note that the type of the vertices is defined as the
    @EndPoint@ of the edges by default.
    -}
    type Vertex g = EndPoint (Edge g)

    -- | A graph with a single vertex and no edges.
    singleton :: Vertex g -> g

    -- | The set of edges of the graph.
    edges :: g -> MS.MultiSet (Edge g)

    -- | The set of vertices of the graph.
    vertices :: g -> MS.MultiSet (Vertex g)

    -- | Add a graph to another graph.
    addGraph :: (Graph g0, Edge g ~ Edge g0) => g0 -> g -> g

    -- | Add an edge to a graph.
    addEdge :: Edge g -> g -> g

{- |
  Check if a vertex is in a graph.

Example:

>>> vertexOf 1 (integerGraph [1, 2, 3] [(1, 2), (2, 3)])
True
>>> vertexOf 4 (integerGraph [1, 2, 3] [(1, 2), (2, 3)])
False
-}
vertexOf :: (Eq a, Graph g, Vertex g ~ a) => a -> g -> Bool
vertexOf v g = v `elem` vertices g

{- |
  Naive implementation of a graph given by a multiset of vertices
and a multiset of edges.
-}
data IntegerGraph
    = IG
        (MS.MultiSet Integer)
        (MS.MultiSet (Integer, Integer))

{- |
  A constructor of the @IntegerGraph@ type.

Example:

>>> integerGraph [1, 2, 3] [(1, 2), (2, 3)]
IntegerGraph(V=[1,2,3], E=[(1,2),(2,3)])
-}
integerGraph :: [Integer] -> [(Integer, Integer)] -> IntegerGraph
integerGraph vs es = IG (MS.fromList vs) (MS.fromList es)

{- |
  The @IntegerGraph@ type is an instance of the @Graph@ typeclass.

Example:

>>> singleton 1 :: IntegerGraph
IntegerGraph(V=[1], E=[])
>>> edges $ integerGraph [1, 2, 3] [(1, 2), (2, 3)]
fromOccurList [((1,2),1),((2,3),1)]
>>> vertices $ integerGraph [1, 2, 3] [(1, 2), (2, 3)]
fromOccurList [(1,1),(2,1),(3,1)]
>>> addGraph (singleton 4 :: IntegerGraph) $ integerGraph [1, 2, 3] [(1, 2), (2, 3)]
IntegerGraph(V=[1,2,3,4], E=[(1,2),(2,3)])
>>> addEdge (3, 2) $ integerGraph [1, 2, 3] [(1, 2), (2, 3)]
IntegerGraph(V=[1,2,3], E=[(1,2),(2,3),(3,2)])
-}
instance Graph IntegerGraph where
    type Edge IntegerGraph = (Integer, Integer)

    singleton v = IG (MS.singleton v) MS.empty

    edges (IG _ es) = es

    vertices (IG vs _) = vs

    addGraph g (IG vs es) =
        IG (vertices g `MS.union` vs) (edges g `MS.union` es)

    addEdge e (IG vs es) =
        IG vs (e `MS.insert` es)

instance Show IntegerGraph where
    show g = "IntegerGraph(V=" ++ vs ++ ", E=" ++ es ++ ")"
      where
        vs = show $ MS.toList $ vertices g
        es = show $ MS.toList $ edges g

----------------------------------------------------------------------

-- * Rooted graphs

----------------------------------------------------------------------

{- |
  A typeclass for rooted graphs which have a distinguished vertex
called the root.
-}
class (Graph g) => RootedGraph g where
    root :: g -> Vertex g

-- | A data type for rooted graphs.
data Rooted g = R (Vertex g) g

instance (Show g, Show (Vertex g)) => Show (Rooted g) where
    show (R r g) = "Rooted" ++ trimmedShowG ++ ", R=" ++ show r ++ ")"
      where
        trimmedShowG = L.init $ show g

instance (Eq (Vertex g), Eq g) => Eq (Rooted g) where
    (R r1 g1) == (R r2 g2) = (r1 == r2) && (g1 == g2)

instance (Graded g) => Graded (Rooted g) where
    grading (R _ g) = grading g

instance (Graph g) => Graph (Rooted g) where
    type Edge (Rooted g) = Edge g
    singleton v = R v $ singleton v
    edges (R _ g) = edges g
    vertices (R _ g) = vertices g
    addGraph g0 (R r g) = R r (addGraph g0 g)
    addEdge e (R r g) = R r (addEdge e g)

instance (Graph g) => RootedGraph (Rooted g) where
    root (R r _) = r

{- |
  A constructor for the @Rooted@ type which checks if the root
  vertex is in the graph.

Example:

>>> rooted (integerGraph [1, 2, 3] [(1, 2), (2, 3)]) 1
RootedIntegerGraph(V=[1,2,3], E=[(1,2),(2,3)], R=1)
-}
rooted :: (Graph g, Eq (Vertex g)) => g -> Vertex g -> Rooted g
rooted g r =
    if r `vertexOf` g
        then R r g
        else error "Root vertex not in graph"

----------------------------------------------------------------------

-- * Grafting

----------------------------------------------------------------------

-- | Two integer graphs are equal if their vertices and edges are equal.
instance Eq IntegerGraph where
    g1 == g2 = (vertices g1 == vertices g2) && (edges g1 == edges g2)

-- | The grading of an integer graph is the number of its vertices.
instance Graded IntegerGraph where
    grading = toInteger . length . vertices

{- |
  Grafing of two graphs.

Example:

>>> g1 = integerGraph [1, 2, 3] [(2, 1), (3, 2)]
>>> graftGraph (rooted g1 1) (integerGraph [4, 5] [(5, 4)])
(1 *^ IntegerGraph(V=[1,2,3,4,5], E=[(1,4),(2,1),(3,2),(5,4)]) + 1 *^ IntegerGraph(V=[1,2,3,4,5], E=[(1,5),(2,1),(3,2),(5,4)]))_5
-}
graftGraph
    :: ( Eq a2
       , Graded a2
       , RootedGraph a1
       , Graph a2
       , Edge a1 ~ Edge a2
       )
    => a1
    -> a2
    -> Vector Integer a2
graftGraph rg1 g2 =
    vectorFromNonDecList $
        map ((1 *^) . graftGraphTo rg1 g2) $
            MS.toList $
                vertices g2

{- |
  Grafing of a rooted graph to a graph at a given vertex.

Example:

>>> g1 = integerGraph [1, 2, 3] [(2, 1), (3, 2)]
>>> graftGraphTo (rooted g1 1) (integerGraph [4, 5] [(5, 4)]) 5
IntegerGraph(V=[1,2,3,4,5], E=[(1,5),(2,1),(3,2),(5,4)])
-}
graftGraphTo
    :: ( RootedGraph a1
       , Graph a2
       , Edge a1 ~ Edge a2
       )
    => a1
    -> a2
    -> Vertex a2
    -> a2
graftGraphTo rg1 g2 v = addGraph rg1 $ addEdge new_edge g2
  where
    new_edge = edge () (root rg1) v

{- |
  Get the first vertex of a list of vertices and remove it from the
  list. This function is used to build graphs from a list of vertices
  using the @State@ monad.

  In practice, it is used to build graphs with unique vertices that
  are collected from a list of vertices.

Example:

>>> runState getVertex [1, 2, 3]
(1,[2,3])
>>> evalState (do {v1 <- getVertex; v2 <- getVertex; return (integerGraph [v1, v2] [(v2, v1)])}) [1, 2, 3]
IntegerGraph(V=[1,2], E=[(2,1)])
-}
getVertex :: State [a] a
getVertex = state $ \l -> (head l, tail l)
