{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : SyntacticTree
Description : Syntactic trees and their compositions are used to implement homomorphisms and are related to the concept of operads.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of syntactic trees is used to represent elements of an algebra as expressions involving generators and operations. This allows us to use syntactic trees to define automorphisms and, if extended, homomorphisms.
-}
module SyntacticTree (
    Operation (..),
    SyntacticTree (..),
    compose,
    symmetricCompose,
    HasSyntacticTree (..),
    eval,
    substitution,
    Substitutable (..),
) where

import Data.List (intercalate, permutations)
import Data.Maybe (fromJust)
import qualified Data.MultiSet as MS
import GradedList
import Output
import RootedTree
import Symbolics

data Operation a = Op
    { name :: String
    , tex :: String
    , arity :: Int
    , func :: [a] -> Vector (VectorScalar a) (VectorBasis a)
    }

instance (Eq a) => Eq (Operation a) where
    (Op n1 _ _ _) == (Op n2 _ _ _) = n1 == n2

data SyntacticTree a
    = Node
        { operation :: Operation a
        , arguments :: [SyntacticTree a]
        }
    | Leaf a
    deriving (Eq)

instance (Graded a) => Graded (SyntacticTree a) where
    grading (Leaf a) = grading a
    grading (Node _ as) = sum $ map grading as

instance (Show a) => Show (SyntacticTree a) where
    show (Leaf a) = show a
    show (Node op as) = (name op) ++ "(" ++ intercalate "," (map show as) ++ ")"

instance (Show a, Texifiable a) => Texifiable (SyntacticTree a) where
    texify = texify . syntacticToPlanar

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

compose
    :: ( Eq a
       , Graded a
       )
    => SyntacticTree a
    -> [SyntacticTree a]
    -> SyntacticTree a
    -> Maybe (SyntacticTree a)
compose _ [] (Leaf y) = Just $ Leaf y
compose _ [y] (Leaf _) = Just y
compose _ _ (Leaf _) = Nothing
compose _ _ (Node op []) = Just $ Node op []
compose x ops (Node op as) = Just $ Node op $ map (\(a, ops_a) -> fromJust $ compose x ops_a a) $ spreadOps ops as
  where
    spreadOps os [a] = [(a, os)]
    spreadOps os (a : as) = (a, take (countSubtrees x a) os) : (spreadOps (drop (countSubtrees x a) os) as)

    countSubtrees x y =
        if x == y
            then 1
            else case y of
                Leaf _ -> 0
                Node _ as -> sum $ map (countSubtrees x) as
                _ -> 0

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

class (IsVector a) => HasSyntacticTree a where
    syn :: a -> SyntacticTree a

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

substitution
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
substitution x gens obj = linear eval $ symmetricCompose (syn x) (map syn gens) $ syn obj

class IsVector t => Substitutable t where
    type Generator t

    substitute :: Generator t -> [t] -> t -> Vector (VectorScalar t) t

graftOp :: (IsVector a, Graftable a) => Operation a
graftOp = Op "graft" "$\\curvearrowright$" 2 $
    \ops -> case ops of
        [x, y] -> graft x y
        _ -> error "graftOp: arity"

concatOp :: (IsVector a, Monoid a) => Operation a
concatOp = Op "concat" "$\\cdot$" (-1) $
    \ops -> vector $ mconcat ops

instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    )
    => HasSyntacticTree [t]
    where
    syn [t] = case (children t) of
        [] -> Leaf [t]
        _ -> Node graftOp [syn (children t), Leaf [buildTree (root t) []]]
    syn ts = Node concatOp $ map (syn . (: [])) ts

instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Ord t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    , Ord (TreeDecoration t)
    )
    => HasSyntacticTree (MS.MultiSet t)
    where
    syn ts = case MS.toList ts of
        [t] -> case (children t) of
            [] -> Leaf $ MS.singleton t
            _ -> Node graftOp [syn (MS.fromList $ children t), Leaf $ MS.singleton $ buildTree (root t) []]
        ts -> Node concatOp $ map (syn . MS.singleton) ts

instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    )
    => Substitutable [t]
    where
    type Generator [t] = TreeDecoration t

    substitute x gens obj = substitution ([buildTree x []]) gens obj

instance
    ( IsVector t
    , IsTree t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Ord t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    , Ord (TreeDecoration t)
    )
    => Substitutable (MS.MultiSet t)
    where
    type Generator (MS.MultiSet t) = TreeDecoration t

    substitute x gens obj = substitution (MS.singleton $ buildTree x []) gens obj
