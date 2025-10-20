{-# LANGUAGE FlexibleContexts  #-}

{- |
Module      : MagmaticProduct
Description : Formulas which use the magmatic product of planar forests: a * b = a B^+(b)
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of formulas which use the magmatic product of planar forests: a * b = a B^+(b)
-}
module MagmaticProduct (
    magIsEmpty,
    magLeft,
    magRight,
    magRoot,
    magBm,
    magBp,
    magProd,
    magButcherProd,
    magShuffle,
    shuffleCross,
    magCK,
    magDecon,
    magCosub,
    coproductCK,
    magPrune,
    buildSyntacticTree,
) where

import Data.List (tails, inits)

import RootedTree
import Symbolics
import GradedList
import SyntacticTree

magIsEmpty :: [t] -> Bool
magIsEmpty [] = True
magIsEmpty _ = False

magLeft :: [t] -> [t]
magLeft = init

magRight :: (IsTree t) => [t] -> [t]
magRight = children . last

magRoot :: (IsTree t) => [t] -> Decoration t
magRoot = RootedTree.root . last

magBm :: (IsTree t) => t -> [t]
magBm = children

magBp :: (IsTree t) => Decoration t -> [t] -> t
magBp c = buildTree c

magProd :: (IsTree t) => Decoration t -> [t] -> [t] -> [t]
magProd c f1 f2 = f1 ++ [magBp c f2]

magButcherProd :: (IsTree t) => t -> t -> t
magButcherProd t1 t2 = magBp c $ magProd c' (magBm t1) (magBm t2)
  where
    c = magRoot [t1]
    c' = magRoot [t2]

magShuffle 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> [t] -> Vector (VectorScalar t) [t]
magShuffle [] f = vector f
magShuffle f [] = vector f
magShuffle f1@(t1:ts1) f2@(t2:ts2) = (vector [t1]) * (magShuffle ts1 f2) + (vector [t2]) * (magShuffle f1 ts2)

shuffleCross
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => Decoration t -> ([t], [t]) -> ([t], [t]) -> Vector (VectorScalar t) ([t], [t])
shuffleCross c (f11, f12) (f21, f22) = bilinear (,) (magShuffle f11 f21) (vector $ magProd c f12 f22)

magCK 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
magCK [] = vector ([], [])
magCK f = (vector (f, [])) + (bilinear (shuffleCross c) (magCK $ magLeft f) (magCK $ magRight f))
  where
    c = magRoot f

magDecon 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
magDecon [] = vector ([], [])
magDecon f = vectorFromList $ map ((*^) 1) $ zip (inits f) (tails f)

magCosub 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => (t -> VectorScalar t) -> [t] -> Vector (VectorScalar t) [t]
magCosub _ [] = vector []
magCosub a f = linear perDecompTerm $ linear perDeconTerm $ linear removeTerm $ magDecon f
  where
    perDeconTerm (f1, f2) = linear (\(f21, f22) -> 1 *^ ((f1, f21), f22)) $ magPrune f2
    perDecompTerm ((f1, f21), f22) = scale (a' f22) $ bilinear (magProd 1) (magCosub a f1) (magCosub a f21)
    a' [t] = a t
    a' _ = 0
    removeTerm (_, []) = Empty
    removeTerm term = vector term


coproductCK 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
coproductCK [] = vector ([], [])
coproductCK [t] = (vector ([t], [])) + (linear perTerm $ coproductCK $ children t)
  where
    perTerm (f1, f2) = (f1, (:[]) $ buildTree c f2)
    c = RootedTree.root t
coproductCK f = morphism (\s -> coproductCK [s]) $ vector f

magPrune 
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
magPrune [] = vector ([], [])
magPrune f = bilinear (shuffleCross c) (magPrune $ magLeft f) (magCK $ magRight f)
  where
    c = magRoot f

-- | Magmatic product operation.
-- data Operation a = Op
--    { name :: String
--    , tex :: String
--    , arity :: Int
--    , func :: [a] -> Vector (VectorScalar a) (VectorBasis a)
--    }
magProdOp
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Show (Decoration t)
       ) => Decoration t -> Operation [t]
magProdOp c = Op ("magprod[" ++ (show c) ++ "]") ("$\\times_" ++ (show c) ++ "$") 2 $
    \ops ->
        case ops of
            [x, y] -> vector $ magProd c x y
            _ -> error $ "magrpodOp " ++ (show c) ++ ": arity"

buildSyntacticTree
    :: ( IsTree t
       , Graded t
       , IsVector t
       , Eq t
       , Eq (VectorScalar t)
       , Num (VectorScalar t)
       , Show (Decoration t)
    ) => [t] -> SyntacticTree [t]
buildSyntacticTree [] = Leaf []
buildSyntacticTree ts = Node (magProdOp c) $ map buildSyntacticTree [magLeft ts, magRight ts]
  where
    c = magRoot ts
