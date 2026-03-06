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
module Core.SyntacticTree (
    Operation (..),
    SyntacticTree (..),
    compose,
    symmetricCompose,
    HasSyntacticTree (..),
    eval,
    substitute,
) where

import Control.Monad.State
import Core.GradedList
import Core.Output
import Core.VectorSpace
import Data.List (intercalate, permutations)
import Data.Maybe (fromJust)

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
instance (Show a) => Texifiable (SyntacticTree a) where
    texifyID _ = "SyntacticTree"
    texify t = "\\forest{" ++ brackets t ++ "}"
      where
        brackets (Node op as) =
            wrap (tex op)
                ++ ( case as of
                        [] -> ""
                        _ -> "[" ++ intercalate "," (map brackets as) ++ "]"
                   )
        brackets (Leaf a) = wrap a
        wrap r = "i_" ++ filter (/= '"') (show r)

instance (IsVector a, Graded a) => IsVector (SyntacticTree a) where
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

  See @IsTree (PlanarTree d)@ instance in @Planar@ module for examples.
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

  See @IsTree (PlanarTree d)@ instance in @Planar@ module for examples.
-}
symmetricCompose
    :: ( IsVector a
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

  See @IsTree (PlanarTree d)@ instance in @Planar@ module for examples.
-}
eval
    :: ( IsVector a
       , VectorBasis a ~ a
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

  See @IsTree (PlanarTree d)@ instance in @Planar@ module for examples.
-}
substitute
    :: ( HasSyntacticTree a
       , IsVector a
       , VectorBasis a ~ a
       )
    => a
    -> [a]
    -> a
    -> Vector (VectorScalar a) a
substitute x gens obj = linear eval $ symmetricCompose (syn x) (map syn gens) $ syn obj
