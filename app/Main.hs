{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import AromaticTree
import Control.Monad.State.Lazy
import Data.Group
import qualified Data.List as L
import Data.Monoid as M
import qualified Data.MultiSet as MS
import Debug.Trace
import GradedList
import Graph
import Numeric.LinearAlgebra as LA
import Output
import RootedTree
import Symbolics as S
import SyntacticTree

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

-------------- Butcher series

bseries
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , Fractional (VectorScalar t)
       )
    => S.Vector (S.VectorScalar t) [t]
    -> ([t] -> S.VectorScalar t)
    -> S.Vector (S.VectorScalar t) [t]
bseries gen coeff = S.renormalize (\_ x -> coeff x) $ expGL gen $ S.vector []

-- Exact solution

expGL
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , Fractional (VectorScalar t)
       )
    => S.Vector (S.VectorScalar t) [t]
    -> S.Vector (S.VectorScalar t) [t]
    -> S.Vector (S.VectorScalar t) [t]
expGL gen start =
    S.vectorFromNonDecList $
        foldr1 (++) $
            map (terms . (\(k, x) -> S.scale (1 / (fromInteger $ product [1 .. k])) x)) $
                zip (1 : [1 ..] :: [Integer]) $
                    iterate (S.bilinear gl gen) start

-- Runge-Kutta methods

-- RK coeffs

v1 = LA.vector $ take 4 [1, 1 ..]

-- RK4
b = LA.vector [1 / 8, 3 / 8, 3 / 8, 1 / 8]

a = LA.matrix 4 [0, 0, 0, 0, 1 / 3, 0, 0, 0, -1 / 3, 1, 0, 0, 1, -1, 1, 0]

rkCoeff
    :: (IsTree t)
    => LA.Matrix LA.R
    -> LA.Vector LA.R
    -> t
    -> LA.R
rkCoeff aij bi t = (<.>) bi $ product $ (v1 :) $ map (rkInternalCoeff aij) $ children t

rkInternalCoeff
    :: (IsTree t)
    => LA.Matrix LA.R
    -> t
    -> LA.Vector R
rkInternalCoeff aij t = (#>) aij $ product $ (v1 :) $ map (rkInternalCoeff aij) $ children t

rkbseries
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       , VectorScalar t ~ LA.R
       , Fractional (VectorScalar t)
       )
    => S.Vector (S.VectorScalar t) [t]
    -> LA.Matrix LA.R
    -> LA.Vector LA.R
    -> S.Vector (S.VectorScalar t) [t]
rkbseries gen aij bi = bseries gen $ product . map (rkCoeff aij bi)

-- DEBUG

vectorFNDL x = vectorFromNonDecList $ trace ("x: " ++ (show $ take 3 x)) x

willHang x y =
    vectorFromNonDecList $
        (terms y) `conc` (terms $ willHang x $ x * y)

wontHang x y = [y] `conc` (wontHang x $ x `conc` y)

conc = (++)

infvec = vectorFromNonDecList [i *^ (take i $ repeat 'c') | i <- [0 ..]]

-- / DEBUG

----------------------- Magmatic product

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

magBp :: (IsTree t, Num (Decoration t)) => [t] -> t
magBp = buildTree 1

magProd :: (IsTree t, Num (Decoration t)) => [t] -> [t] -> [t]
magProd f1 f2 = f1 ++ [magBp f2]

magButcherProd :: (IsTree t, Num (Decoration t)) => t -> t -> t
magButcherProd t1 t2 = magBp $ (magBm t1) `magProd` (magBm t2)

magShuffle 
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> [t] -> S.Vector (S.VectorScalar t) [t]
magShuffle [] f = S.vector f
magShuffle f [] = S.vector f
magShuffle f1@(t1:ts1) f2@(t2:ts2) = (S.vector [t1]) * (magShuffle ts1 f2) + (S.vector [t2]) * (magShuffle f1 ts2)

shuffleCross
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => ([t], [t]) -> ([t], [t]) -> S.Vector (S.VectorScalar t) ([t], [t])
shuffleCross (f11, f12) (f21, f22) = S.bilinear (,) (magShuffle f11 f21) (S.vector $ magProd f12 f22)

magCK 
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> S.Vector (S.VectorScalar t) ([t], [t])
magCK [] = S.vector ([], [])
magCK f = (S.vector (f, [])) + (S.bilinear shuffleCross (magCK $ magLeft f) (magCK $ magRight f))

coproductCK 
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> S.Vector (S.VectorScalar t) ([t], [t])
coproductCK [] = S.vector ([], [])
coproductCK [t] = (S.vector ([t], [])) + (linear perTerm $ coproductCK $ children t)
  where
    perTerm (f1, f2) = (f1, (:[]) $ buildTree 1 f2)
coproductCK f = morphism (\s -> coproductCK [s]) $ S.vector f

magPrune 
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> S.Vector (S.VectorScalar t) ([t], [t])
magPrune [] = S.vector ([], [])
magPrune f = bilinear shuffleCross (magPrune $ magLeft f) (magCK $ magRight f)

{--
magProd
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       )
    => [t] -> [t] -> S.Vector (S.VectorScalar t) [t]
magProd f1 f2 = S.vector $ f1 ++ [buildTree 1 f2]

-- | Magmatic product operation.
magProdOp
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
       ) => Operation [t]
magProdOp = Op "magprod" "$\\times_\\bullet$" 2 $
    \ops ->
        case ops of
            [x, y] -> magProd x y
            _ -> error "magrpodOp: arity"

buildSyntacticTree
    :: ( IsTree t
       , Graded t
       , S.IsVector t
       , Eq t
       , Eq (S.VectorScalar t)
       , Num (S.VectorScalar t)
       , Num (Decoration t)
    ) => [t] -> SyntacticTree [t]
buildSyntacticTree [] = Leaf []
buildSyntacticTree ts = Node magProdOp $ map buildSyntacticTree [magLeft ts, magRight ts]

--}


main = do
    putStrLn "Graph 1"
    print g1
    putStrLn "Rooted Graph 1"
    print rg1
    putStrLn "Graph 2"
    print g2
