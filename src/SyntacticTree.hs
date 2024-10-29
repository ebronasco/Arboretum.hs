{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : SyntacticTree
Description : Syntactic trees and their compositions are used to implement automorphisms and are related to the concept of operads.
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of syntactic trees is used to represent elements of an
algebra as expressions involving generators and operations. This
allows us to use syntactic trees to define automorphisms and, if
extended, homomorphisms.
-}
module SyntacticTree (
    Operation (..),
    SyntacticTree (..),
    compose,
    symmetricCompose,
    HasSyntacticTree (..),
    eval,
    substitute,
    graftOp,
    concatOp,
) where

import Control.Monad.State
import Data.List (intercalate, permutations)
import Data.Maybe (fromJust)
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics

{- $setup
>>> l1 = Leaf [PT 1 []]
>>> l2 = Leaf [PT 2 []]
>>> l3 = Leaf [PT 3 []]
>>> l4 = Leaf [PT 4 []]
-}

{- |
  An operation is a function that takes a list of operands and
  returns a vector. The value of @arity@ is the number of operands
  accepted by the operation. The @func@ performs the actual
  operation. The @tex@ is the LaTeX representation of the operation.

!!! The name of the operation must be unique.
-}
data Operation a = Op
    { name :: String
    , tex :: String
    , arity :: Int
    , func :: [a] -> Vector (VectorScalar a) (VectorBasis a)
    }

-- | Two operations are equal if their names are equal.
instance (Eq a) => Eq (Operation a) where
    (Op n1 _ _ _) == (Op n2 _ _ _) = n1 == n2

{- | Syntactic tree is a tree with operations at the nodes and
operands at the leaves.
-}
data SyntacticTree a
    = Node (Operation a) [SyntacticTree a]
    | Leaf a
    deriving (Eq)

-- | Grading is the sum of gradings of the operands.
instance (Graded a) => Graded (SyntacticTree a) where
    grading (Leaf a) = grading a
    grading (Node _ as) = sum $ map grading as

instance (Show a) => Show (SyntacticTree a) where
    show (Leaf a) = show a
    show (Node op as) = name op ++ "(" ++ intercalate "," (map show as) ++ ")"

{- | Use the representation of syntactic tree as a planar tree to
generate LaTeX code.
-}
instance (Show a, Texifiable a) => Texifiable (SyntacticTree a) where
    texify = texify . syntacticToPlanar
      where
        syntacticToPlanar :: (Show a) => SyntacticTree a -> PlanarTree String
        syntacticToPlanar (Leaf a) = PT (show a) []
        syntacticToPlanar (Node op as) = PT (tex op) $ map syntacticToPlanar as

instance
    ( IsVector a
    , Eq (VectorScalar a)
    , Num (VectorScalar a)
    , Eq a
    , Graded a
    )
    => IsVector (SyntacticTree a)
    where
    type VectorScalar (SyntacticTree a) = VectorScalar a
    type VectorBasis (SyntacticTree a) = SyntacticTree a

    vector = vector . (1 *^)

{- |
  Replace the operands which are equal to the syntactic tree @x@ of a
  syntactic tree @y@ with the given list of syntactic trees @ops@. The
  operands are replaced in the order they appear.

  The function returns @Nothing@ if the number of syntactic trees in
  the list @ops@ is different from the number of operands in the
  syntactic tree @y@.

Examples:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> compose l1 [l3, l4] st
Just graft([3],graft([2],[4]))
>>> compose l1 [l3] st
Nothing
>>> compose l1 [l3, l4, l4] st
Nothing
-}
compose
    :: ( Eq a
       , Graded a
       )
    => SyntacticTree a
    -> [SyntacticTree a]
    -> SyntacticTree a
    -> Maybe (SyntacticTree a)
compose x ops y = checkStateEmpty $ runState (compose' y) ops
  where
    checkStateEmpty (res, []) = res
    checkStateEmpty _ = Nothing
    compose' y' =
        if x == y'
            then do
                ops' <- get
                case ops' of
                    [] -> return Nothing
                    o : os -> do
                        put os
                        return $ Just o
            else case y' of
                Leaf a -> return $ Just $ Leaf a
                Node op as -> do
                    as' <- mapM compose' as
                    if Nothing `elem` as'
                        then return Nothing
                        else return $ Just $ Node op $ map fromJust as'

{- |
  The same as @compose@ but we sum over all permutations of the list
  of syntactic trees and return the result as a vector.

Examples:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> symmetricCompose l1 [l3, l4] st
(1 *^ graft([3],graft([2],[4])) + 1 *^ graft([4],graft([2],[3])))_3
>>> symmetricCompose l1 [l3] st
_0
>>> symmetricCompose l1 [l3, l4, l4] st
_0
-}
symmetricCompose
    :: ( IsVector a
       , Eq (VectorScalar a)
       , Num (VectorScalar a)
       , Eq a
       , Graded a
       )
    => SyntacticTree a
    -> [SyntacticTree a]
    -> SyntacticTree a
    -> Vector (VectorScalar (SyntacticTree a)) (SyntacticTree a)
symmetricCompose x ops obj =
    mconcat
        $ map
            ( \perm_ops -> case compose x perm_ops obj of
                Just g -> vector (1 *^ g)
                Nothing -> vector Zero
            )
        $ permutations ops

-- | A class for types that can be represented as syntactic trees.
class (IsVector a) => HasSyntacticTree a where
    syn :: a -> SyntacticTree a

{- |
  Evaluate a syntactic tree.

Examples:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> v = symmetricCompose l1 [l3, l4] st
>>> eval st
(1 *^ [1[2[1]]] + 1 *^ [1[1,2]])_3
>>> linearGraded eval v
(1 *^ [4[2[3]]] + 1 *^ [4[3,2]] + 1 *^ [3[2[4]]] + 1 *^ [3[4,2]])_3
-}
eval
    :: ( IsVector a
       , VectorBasis a ~ a
       , Num (VectorScalar a)
       , Eq (VectorScalar a)
       , Eq a
       , Graded a
       )
    => SyntacticTree a
    -> Vector (VectorScalar a) a
eval (Leaf a) = vector a
eval (Node op as) = linear (func op) $ product $ map (linear (: []) . eval) as

{- |
  Substitute the subexpression @x@ of @obj@ with the given list of
  expressions @gens@ in all possible ways and return the result as a
  vector.

  If the number of expressions in the list @gens@ is different from
  the number of occurrences of the subexpression @x@ in @obj@, the
  function returns a zero vector.

Examples:

>>> expr1 = [PT 1 [PT 2 [], PT 1 []]]
>>> expr2 = [PT 3 [PT 3 []]]
>>> substitute [PT 2 []] [expr2] expr1
(1 *^ [1[3[3],1]])_4
>>> substitute [PT 1 []] [expr2,expr2] expr1
(2 *^ [3[3[2,3[3]]]] + 2 *^ [3[2,3[3[3]]]] + 2 *^ [3[3[3],3[2]]] + 2 *^ [3[2,3[3],3]])_5
>>> substitute [PT 1 []] [expr2,expr2,expr2] expr1
_0
>>> substitute [PT 1 []] [] expr1
_0
-}
substitute
    :: ( HasSyntacticTree a
       , IsVector a
       , Eq (VectorScalar a)
       , Num (VectorScalar a)
       , Eq a
       , Graded a
       , VectorBasis a ~ a
       )
    => a
    -> [a]
    -> a
    -> Vector (VectorScalar a) a
substitute x gens obj = linear eval $ symmetricCompose (syn x) (map syn gens) $ syn obj

-- | Grafting operation.
graftOp :: (IsVector a, Graftable a) => Operation a
graftOp = Op "graft" "$\\curvearrowright$" 2 $
    \ops ->
        case ops of
            [x, y] -> graft x y
            _ -> error "graftOp: arity"

-- | Concatenation operation.
concatOp :: (IsVector a, Monoid a) => Operation a
concatOp = Op "concat" "$\\cdot$" (-1) (vector . mconcat)

{- |
  Construct a syntactic tree of a list of trees.

Examples:

>>> f = [PT 1 [PT 2 [], PT 3 []], PT 4 []]
>>> syn f
concat(graft(concat([2],[3]),[1]),[4])
-}
instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Eq (Decoration t)
    , Graded (Decoration t)
    )
    => HasSyntacticTree [t]
    where
    syn [t] = case children t of
        [] -> Leaf [t]
        _ -> Node graftOp [syn (children t), Leaf [buildTree (root t) []]]
    syn ts = Node concatOp $ map (syn . (: [])) ts

{- |
  Construct a syntactic tree of a multiset of trees.

Examples:

>>> f = nonplanar [PT 1 [PT 2 [], PT 3 []], PT 4 []] :: MS.MultiSet (Tree Integer)
>>> syn f
concat(graft(concat(fromOccurList [(2,1)],fromOccurList [(3,1)]),fromOccurList [(1,1)]),fromOccurList [(4,1)])
-}
instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Ord t
    , Eq (Decoration t)
    , Graded (Decoration t)
    , Ord (Decoration t)
    )
    => HasSyntacticTree (MS.MultiSet t)
    where
    syn ts = case MS.toList ts of
        [t] -> case children t of
            [] -> Leaf $ MS.singleton t
            _ -> Node graftOp [syn (MS.fromList $ children t), Leaf $ MS.singleton $ buildTree (root t) []]
        ts' -> Node concatOp $ map (syn . MS.singleton) ts'
