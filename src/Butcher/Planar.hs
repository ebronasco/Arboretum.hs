{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : MagmaticProduct
Description : Formulas which use the magmatic product of planar forests: a * b = a B^+(b)
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of formulas which use the magmatic product of planar forests: a * b = a B^+(b)
-}
module Butcher.Planar (
    PlanarTree (..),
    magLeft,
    magRight,
    magRoot,
    magProduct,
    magButcher,
    shuffleCross,
    magCosub,
    magPrune,
    buildSyntacticTree,
) where

import Core.GradedList
import Core.VectorSpace
import Core.Algebra
import Core.SyntacticTree
import Butcher.Tree as T

{- $setup
  Integer Tree From Brackets
>>> itfb str = fromBrackets str :: PlanarTree Integer

  Integer Forest From Brackets
>>> iffb str = fromBrackets str :: [PlanarTree Integer]
-}

---------------------------------------------------------------------

-- * Planar trees

---------------------------------------------------------------------

{- | Planar trees are represented as a tree with a root and a list of
branches which are planar trees themselves.
-}
data PlanarTree d = PT
    { planarRoot :: d
    , planarBranches :: [PlanarTree d]
    }
    deriving (Eq)

instance IsDecorated (PlanarTree d) where
    type Decoration (PlanarTree d) = d

instance (Graded d) => IsTree (PlanarTree d) where
    root = planarRoot
    branches = planarBranches

    buildTree = PT

instance (Graded d) => HasBracketNotation (PlanarTree d) where
    toBracketsWith = treeToBracketsWith
    fromBracketsWith = treeFromBracketsWith

instance (Show d, Graded d) => Show (PlanarTree d) where
    show = toBrackets 

-- | Planar trees are vectors with integer coefficients.
instance (Eq d, Graded d) => IsVector (PlanarTree d) where
    type VectorScalar (PlanarTree d) = Integer
    type VectorBasis (PlanarTree d) = PlanarTree d

    vector = vector . (1 *^)

{- |
  Grading of a planar tree is the sum of gradings of the nodes.

Example:

>>> grading $ itfb "1[2,34]"
3

Note: the grading of an integer is the number of digits with @0@ having grading @0@.
-}
instance (Graded d) => Graded (PlanarTree d) where
    grading (PT r xs) = grading r + sum (map grading xs)


magLeft :: [t] -> [t]
magLeft = init

magRight :: (IsTree t) => [t] -> [t]
magRight = branches . last

magRoot :: (IsTree t) => [t] -> Decoration t
magRoot = T.root . last

magProduct :: (IsTree t) => Decoration t -> [t] -> [t] -> [t]
magProduct c f1 f2 = f1 ++ [buildTree c f2]

magButcher :: (IsTree t) => t -> t -> t
magButcher t1 t2 = buildTree c $ magProduct c' (branches t1) (branches t2)
  where
    c = magRoot [t1]
    c' = magRoot [t2]

shuffleCross
    :: ( IsTree t
       , IsVector t
       )
    => Decoration t
    -> ([t], [t])
    -> ([t], [t])
    -> Vector (VectorScalar t) ([t], [t])
shuffleCross c (f11, f12) (f21, f22) = bilinear (,) (shuffle f11 f21) (vector $ magProduct c f12 f22)

instance (IsTree t, IsVector t) => CanConnesKreimer [t] where
    connesKreimer [] = vector ([], [])
    connesKreimer f = vector (f, []) + bilinear (shuffleCross c) (connesKreimer $ magLeft f) (connesKreimer $ magRight f)
      where
        c = magRoot f

magCosub
    :: ( IsTree t
       , IsVector t
       )
    => [Decoration t]
    -> (Decoration t -> t -> VectorScalar t)
    -> [t]
    -> Vector (VectorScalar t) [t]
magCosub _ _ [] = vector []
magCosub cs a f = sum $ map (\c -> linear (perDecompTerm c) $ linear perDeconTerm $ deconcatenate' f) cs
  where
    perDeconTerm (f1, f2) =
        linear (\(f21, f22) -> 1 *^ ((f1, f21), f22)) $
            magPrune f2
    perDecompTerm c ((f1, f21), f22) =
        scale (a' c f22) $
            bilinear (magProduct c) (magCosub cs a f1) (magCosub cs a f21)
    a' c [t] = a c t
    a' _ _ = 0
    deconcatenate' = linear removeTerm . deconcatenate
      where
        removeTerm (_, []) = Empty
        removeTerm term = vector term

magPrune
    :: ( IsTree t
       , IsVector t
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
magPrune [] = vector ([], [])
magPrune f = bilinear (shuffleCross c) (magPrune $ magLeft f) (connesKreimer $ magRight f)
  where
    c = magRoot f

{- | Magmatic product operation.
data Operation a = Op
   { name :: String
   , tex :: String
   , arity :: Int
   , func :: [a] -> Vector (VectorScalar a) (VectorBasis a)
   }
-}
magProductOp
    :: ( IsTree t
       , IsVector t
       , Show (Decoration t)
       )
    => Decoration t -> Operation [t]
magProductOp c = Op ("magprod[" ++ show c ++ "]") ("$\\times_" ++ show c ++ "$") 2 $
    \case
        [x, y] -> vector $ magProduct c x y
        _ -> error $ "magrpodOp " ++ show c ++ ": arity"

buildSyntacticTree
    :: ( IsTree t
       , IsVector t
       , Show (Decoration t)
       )
    => [t] -> SyntacticTree [t]
buildSyntacticTree [] = Leaf []
buildSyntacticTree ts = Node (magProductOp c) $ map buildSyntacticTree [magLeft ts, magRight ts]
  where
    c = magRoot ts
