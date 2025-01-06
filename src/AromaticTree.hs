{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : AromaticTree
Description : Implementation of non-planar aromatic trees, forests, their grafting, divergence, and substitution.
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental
-}
module AromaticTree (
    Cycle (Cycle),
    divergence,
    PlanarAromatic,
    Aromatic,
) where

import Control.Monad.State (evalState, get, put)
import Data.Bifunctor (bimap, second)
import qualified Data.List as L
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics
import SyntacticTree

{- $setup
  Integer Forest From Brackets
>>> iffb str = fromBrackets read str :: [PlanarTree Integer]

  Non-Planar Integer Forest From Brackets
>>> npiffb str = fromBrackets read str :: MS.MultiSet (Tree Integer)

  Integer Cycle From Brackets
>>> icfb str = fromBrackets read str :: Cycle (PlanarTree Integer)

  Non-Planar Integer Cycle From Brackets
>>> npicfb str = fromBrackets read str :: Cycle (Tree Integer)

  Planar Aromatic Integer Forest From Brackets
>>> paiffb st = fromBrackets read st :: PlanarAromatic (PlanarTree Integer)

  Aromatic Integer Forest From Brackets
>>> aiffb st = fromBrackets read st :: Aromatic (Tree Integer)
-}

----------------------------------------------------------------------

-- * Cycles

----------------------------------------------------------------------

{- |
  Orbit of a list under cyclic permutation.

Examples:

>>> circulate [1, 2, 3]
[[1,2,3],[2,3,1],[3,1,2]]
>>> circulate [1, 2, 3, 4]
[[1,2,3,4],[2,3,4,1],[3,4,1,2],[4,1,2,3]]
-}
circulate :: [a] -> [[a]]
circulate [] = [[]]
circulate l =
    take (length l) $
        map (take (length l)) (L.tails (cycle l))

-- | A cycle is a list of elements up to cyclic permutation.
newtype Cycle a = Cycle {unCycle :: [a]}

{- |
  Check if two cycles are equal up to cyclic permutation.

Examples:

>>> Cycle [1, 2, 3] == Cycle [3, 1, 2]
True
>>> Cycle [1, 2, 3] == Cycle [3, 2, 1]
False
-}
instance (Eq a) => Eq (Cycle a) where
    (Cycle a) == (Cycle b) = a `elem` circulate b

{- |
  Compare two cycles by comparing the maximums of their cyclic
  permutation orbits.

Examples:

>>> compare (Cycle [1, 2, 3]) (Cycle [3, 1, 2])
EQ
>>> compare (Cycle [1, 3, 2]) (Cycle [3, 1, 2])
GT
-}
instance (Ord a) => Ord (Cycle a) where
    compare (Cycle a) (Cycle b) = compare (maximum $ circulate a) (maximum $ circulate b)

instance Functor Cycle where
    fmap f (Cycle l) = Cycle $ map f l

instance (Show a) => Show (Cycle a) where
    show (Cycle l) = "(" ++ init (tail $ show l) ++ ")"

instance (Graded a) => Graded (Cycle a) where
    grading (Cycle l) = sum $ map grading l

instance
    ( IsVector a
    , Num (VectorScalar a)
    , Eq (VectorScalar a)
    , Eq a
    , Graded a
    )
    => IsVector (Cycle a)
    where
    type VectorScalar (Cycle a) = VectorScalar a
    type VectorBasis (Cycle a) = Cycle a

    vector = vector . (1 *^)

instance (IsDecorated t) => IsDecorated (Cycle t) where
    type Decoration (Cycle t) = Decoration t

{- |
  Represent a cycle in bracket notation or parse a cycle from bracket
  notation.

Examples:

>>> toBrackets show $ Cycle $ iffb "1[2,3],2[3,4]"
"(1[2,3],2[3,4])"
>>> fromBrackets read "(1[2,3],2[3,4])" :: Cycle (PlanarTree Integer)
(1[2,3],2[3,4])
-}
instance (IsTree t, HasBracketNotation t) => HasBracketNotation (Cycle t) where
    toBrackets f a = "(" ++ L.intercalate "," (map (toBrackets f) $ unCycle a) ++ ")"

    fromBrackets f = Cycle . fromBrackets f . escapeParentheses
      where
        escapeParentheses [] = []
        escapeParentheses str =
            if head str == '(' && last str == ')'
                then init $ tail str
                else str

{- |
  Use brakcet notation of cycles to generate TeX code.

Examples:

>>> texify $ Cycle $ iffb "1[2,3],2[3,4]"
"\\forest{(1[2,3],2[3,4])}"
-}
instance (Texifiable (Decoration t), IsTree t, HasBracketNotation t) => Texifiable (Cycle t) where
    texify c = "\\forest{" ++ toBrackets texify c ++ "}"

----------------------------------------------------------------------

-- * Planar Aromatic Forest

----------------------------------------------------------------------

type PlanarAromatic t =
    ( [Cycle t]
    , [t]
    )

{- |
  Represent a planar aromatic forest in bracket notation or parse a
  planar aromatic forest from bracket notation.

Examples:

>>> af = ([icfb "(1[2,3],4[5])", icfb "(6[7])"], iffb "8[9],10")
>>> toBrackets show af
"(1[2,3],4[5]),(6[7]),8[9],10"
>>> fromBrackets read "(1[2,3],4[5]),(6[7]),8[9],10" :: PlanarAromatic (PlanarTree Integer)
([(1[2,3],4[5]),(6[7])],[8[9],10])
-}
instance (IsTree t, HasBracketNotation t) => HasBracketNotation (PlanarAromatic t) where
    toBrackets f (ma, ts) =
        L.intercalate "," $
            map (toBrackets f) ma ++ map (toBrackets f) ts

    fromBrackets f =
        bimap
            (map (fromBrackets f))
            (concatMap (fromBrackets f))
            . evalState splitAromasAndTrees
      where
        splitAromasAndTrees = do
            str <- get

            let (forest_str, rest) = break (== '(') str
            let (aroma_str, rest') = break (== ')') rest

            let forest_str' =
                    if not (null forest_str) && last forest_str == ','
                        then init forest_str
                        else forest_str
            let aroma_str' = aroma_str ++ if null rest' then "" else ")"
            let rest'' = if null rest' then "" else tail rest'
            let rest''' =
                    if not (null rest'') && head rest'' == ','
                        then tail rest''
                        else rest''

            put rest'''

            (as, fs) <- case rest''' of
                [] -> return ([], [])
                _ -> splitAromasAndTrees

            let as' = if null aroma_str' then as else aroma_str' : as
            let fs' = if null forest_str' then fs else forest_str' : fs

            return (as', fs')

----------------------------------------------------------------------

-- * Divergence

----------------------------------------------------------------------

{- |
  Compute the list of all pairs of an element and the rest of the list.

Examples:

>>> elemComp [1, 2, 3]
[(1,[2,3]),(2,[1,3]),(3,[1,2])]
-}
elemComp :: [a] -> [(a, [a])]
elemComp [] = []
elemComp (x : xs) = (x, xs) : map (second (x :)) (elemComp xs)

{- |
  Build forests along the paths from the root to the vertices.

Examples:

>>> branchPaths $ head $ iffb "1[2,3]"
[[1[2,3]],[1[3],2],[1[2],3]]
>>> branchPaths $ head $ iffb "1[2[3],4]"
[[1[2[3],4]],[1[4],2[3]],[1[4],2,3],[1[2[3]],4]]
-}
branchPaths :: (IsTree t) => t -> [[t]]
branchPaths t = [t] : recurs (map (second $ buildTree (root t)) $ elemComp $ children t)
  where
    recurs = concatMap (\(x, y) -> map (y :) (branchPaths x))

{- |
  Compute the divergence of a planar aromatic tree by connecting the
  root to the vertices.

Examples:

>>> divergence $ paiffb "1[2,3]"
(1 *^ ([(1[2,3])],[]) + 1 *^ ([(1[3],2)],[]) + 1 *^ ([(1[2],3)],[]))_3
>>> divergence $ paiffb "1[2[3],4]"
(1 *^ ([(1[2[3],4])],[]) + 1 *^ ([(1[4],2[3])],[]) + 1 *^ ([(1[4],2,3)],[]) + 1 *^ ([(1[2[3]],4)],[]))_4
>>> divergence $ paiffb "(1),1"
(1 *^ ([(1[1])],[]) + 1 *^ ([(1),(1)],[]))_2
>>> divergence $ paiffb "(1),1[2,3]"
(1 *^ ([(1[1[2,3]])],[]) + 1 *^ ([(1[2,3]),(1)],[]) + 1 *^ ([(1[3],2),(1)],[]) + 1 *^ ([(1[2],3),(1)],[]))_4
>>> divergence $ paiffb "1[2,3],4,(5)"
(1 *^ ([(5)],[4[1[2,3]]]) + 1 *^ ([(5[1[2,3]])],[4]) + 1 *^ ([(1[2,3]),(5)],[4]) + 1 *^ ([(1[3],2),(5)],[4]) + 1 *^ ([(1[2],3),(5)],[4]))_5
-}
divergence
    :: ( IsDecorated t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       )
    => PlanarAromatic t
    -> Vector (VectorScalar t) (PlanarAromatic t)
divergence (_, []) = vector Zero
divergence (ma, t : ts) = (([], [t]) `graft` (ma, ts)) + linear ((,ts) . (: ma)) (divergenceT t)
  where
    divergenceT t' = mconcat $ map (vector . Cycle) $ branchPaths t'

----------------------------------------------------------------------

-- * Grafting

----------------------------------------------------------------------

{- |
  Graft a planar rooted forest onto a multi-aroma.

Examples:

>>> graftOnMultiAroma (iffb "1") [icfb "(1,1)"]
(2 *^ [(1,1[1])])_3
>>> graftOnMultiAroma (iffb "1") [icfb "(1,2)"]
(1 *^ [(1,2[1])] + 1 *^ [(1[1],2)])_3
>>> graftOnMultiAroma (iffb "1,2") [icfb "(1,2)"]
(1 *^ [(1,2[1,2])] + 1 *^ [(1[1],2[2])] + 1 *^ [(1[2],2[1])] + 1 *^ [(1[1,2],2)])_4
>>> graftOnMultiAroma (iffb "1") [icfb "1,1", icfb "1,2"]
(1 *^ [(1,1),(1,2[1])] + 1 *^ [(1,1),(1[1],2)] + 2 *^ [(1,1[1]),(1,2)])_5
-}
graftOnMultiAroma
    :: ( IsDecorated t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       )
    => [t]
    -> [Cycle t]
    -> Vector (VectorScalar t) [Cycle t]
graftOnMultiAroma [] ma = vector (1 *^ ma)
graftOnMultiAroma _ [] = vector Zero
graftOnMultiAroma f [a] = linear ((1 *^) . (: []) . Cycle) $ (f `graft`) $ unCycle a
graftOnMultiAroma f (a : ma) = linear perCoproductTerm $ deshuffleCoproduct f
  where
    perCoproductTerm (x, y) = (x `graftOnMultiAroma` [a]) * (y `graftOnMultiAroma` ma)

{- |
  Graft two aromatic planar forests.

Examples:

>>> graft (paiffb "(1),1") (paiffb "(2),2")
(1 *^ ([(1),(2)],[2[1]]) + 1 *^ ([(1),(2[1])],[2]))_4
-}
instance
    ( IsDecorated t
    , Eq (Decoration t)
    , Graded (Decoration t)
    , IsTree t
    , IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    )
    => Graftable (PlanarAromatic t)
    where
    graft (ma1, f1) (ma2, f2) =
        vector (ma1, [])
            * linear perCoproductTerm (deshuffleCoproduct f1)
      where
        perCoproductTerm (x, y) =
            linear (,[]) (x `graftOnMultiAroma` ma2)
                * linear ([],) (y `graft` f2)

----------------------------------------------------------------------

-- * Aromatic Forest

----------------------------------------------------------------------

type Aromatic t =
    ( MS.MultiSet (Cycle t)
    , MS.MultiSet t
    )

instance (Planarable t) => Planarable (Cycle t) where
    type Planar (Cycle t) = Cycle (Planar t)

    planar = Cycle . map planar . unCycle
    nonplanar = Cycle . map nonplanar . unCycle

{- |
  Represent an aromatic forest in bracket notation or parse an aromatic
  forest from bracket notation.

Examples:

>>> toBrackets show $ aiffb "(1,2),(3[4]),5[6]"
"(1,2),(3[4]),5[6]"
>>> fromBrackets read "(1,2),(3[4]),5[6]" :: Aromatic (Tree Integer)
(fromOccurList [((1,2),1),((3[4]),1)],fromOccurList [(5[6],1)])
-}
instance
    ( Ord t
    , Planarable t
    , IsTree t
    , IsDecorated t
    , Decoration t ~ Decoration (Planar (Aromatic t))
    , HasBracketNotation t
    , HasBracketNotation (Planar (Aromatic t))
    )
    => HasBracketNotation (Aromatic t)
    where
    toBrackets f = toBrackets f . planar

    fromBrackets f = nonplanar . fromBrackets f

----------------------------------------------------------------------

-- * Substitution

----------------------------------------------------------------------

-- ** Mark

data Marked a = Marked a | Mark deriving (Eq)

instance (Show a) => Show (Marked a) where
    show (Marked a) = "m" ++ show a
    show Mark = "x"

instance (Graded a) => Graded (Marked a) where
    grading (Marked a) = grading a
    grading Mark = 0

instance (Ord a) => Ord (Marked a) where
    compare (Marked a) (Marked b) = compare a b
    compare Mark Mark = EQ
    compare Mark _ = LT
    compare _ Mark = GT

instance (Texifiable a) => Texifiable (Marked a) where
    texify (Marked a) = texify a
    texify Mark = "x"

class Markable a where
    type Marked' a

    mark :: a -> Marked' a
    unmark :: Marked' a -> a

instance (Markable a) => Markable [a] where
    type Marked' [a] = [Marked' a]

    mark = map mark
    unmark = map unmark

instance (Markable a, Ord a, Ord (Marked' a)) => Markable (MS.MultiSet a) where
    type Marked' (MS.MultiSet a) = MS.MultiSet (Marked' a)

    mark = MS.map mark
    unmark = MS.map unmark

instance (Markable a, Markable b) => Markable (a, b) where
    type Marked' (a, b) = (Marked' a, Marked' b)

    mark (a, b) = (mark a, mark b)
    unmark (a, b) = (unmark a, unmark b)

instance (Markable a) => Markable (Cycle a) where
    type Marked' (Cycle a) = Cycle (Marked' a)

    mark = Cycle . mark . unCycle
    unmark = Cycle . unmark . unCycle

instance Markable (PlanarTree d) where
    type Marked' (PlanarTree d) = PlanarTree (Marked d)

    mark (PT r c) = PT (Marked r) (mark c)
    unmark (PT (Marked r) c) = PT r (unmark c)
    unmark (PT Mark _) = error "Cannot unmark a marked vertex"

instance (Ord d) => Markable (Tree d) where
    type Marked' (Tree d) = Tree (Marked d)

    mark (T r c) = T (Marked r) (mark c)
    unmark (T (Marked r) c) = T r (unmark c)
    unmark (T Mark _) = error "Cannot unmark a marked vertex"

{- |
  Build a syntactic tree for planar aromatic forest.

Examples:

>>> syn $ mark $ paiffb "(1),1"
concat(trace(graft(([],[x]),([],[m1]))),([],[m1]))
>>> syn $ mark $ paiffb "(1[2]),(3,4[5]),6[7],8"
concat(trace(graft(concat(([],[x]),([],[m2])),([],[m1]))),trace(graft(graft(concat(([],[x]),([],[m5])),([],[m4])),([],[m3]))),graft(([],[m7]),([],[m6])),([],[m8]))
-}
instance
    ( IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , IsTree t
    , Decoration t ~ Marked d
    , Eq d
    , Graded d
    )
    => HasSyntacticTree (PlanarAromatic t)
    where
    syn ([], []) = Node concatOp []
    syn ([Cycle ts], []) = Node traceOp [syn $ ([],) $ (: []) $ breakCycle ts]
      where
        breakCycle [] = buildTree Mark []
        breakCycle (t : ts') = addBranch (breakCycle ts') t
        addBranch b t = buildTree (root t) (b : children t)
    syn ([], [t]) = case children t of
        [] -> Leaf ([], [t])
        bs -> Node graftOp [syn ([], bs), Leaf ([], [buildTree (root t) []])]
    syn (as, ts) =
        Node concatOp $
            map (syn . (,[]) . (: [])) as
                ++ map (syn . ([],) . (: [])) ts

{- |
  Operation used in the syntactic tree to represent the trace
  operation, that is, the connection of the root to the marked
  vertex.

Examples:

>>> func traceOp $ [([], [PT (Marked 1) [PT Mark [], PT (Marked 2) []]])]
(1 *^ ([(m1[m2])],[]))_2
>>> func traceOp $ [([Cycle [PT (Marked 3) [PT (Marked 4) [PT Mark []]]]], [PT (Marked 1) [PT (Marked 2) []]])]
(1 *^ ([(m3[m4[m1[m2]]])],[]))_4
-}
traceOp
    :: ( IsTree t
       , Decoration t ~ Marked d
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq d
       , Graded d
       )
    => Operation (PlanarAromatic t)
traceOp = Op "trace" "$Tr$" 1 $
    \l -> case l of
        [f] -> connectRootToMarked f
        _ -> error "Trace operation takes one argument"
  where
    connectRootToMarked (_, []) = error "Cannot trace a forest without roots"
    connectRootToMarked (as, [t]) = case searchMarkTree (as, t) of
        Nothing -> searchMarkAroma (as, t)
        Just x -> vector x
    connectRootToMarked (_, _) = error "Cannot trace a forest with multiple roots"
    searchMarkTree (as, t) = case filter ((== buildTree Mark []) . last) $ branchPaths t of
        [] -> Nothing
        l -> Just $ (,[]) $ (: as) $ Cycle $ init $ head l
    searchMarkAroma (as, t) = vector $ (,[]) $ map searchMarkAroma' as
      where
        searchMarkAroma' (Cycle ts) = Cycle $ map searchMarkAroma'' ts
        searchMarkAroma'' t2 =
            if t2 == buildTree Mark []
                then t
                else buildTree (root t2) $ map searchMarkAroma'' $ children t2
