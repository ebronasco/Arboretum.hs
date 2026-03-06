{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module      : MagmaticProduct
Description : Implementation of the planar trees, forests, and the related functions
                including the magmatic product and the related formulas.
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

See Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Magmatic product and the related formulas are introduced in Section 4 of the paper
referenced above.

We implement only those formulas which are clearly "better" than the alternatives
which do not use the magmatic product. In particular, the magmatic product gives
nice formulas for:
 - the planar factorial,
 - planar Connes-Kreimer coproduct,
 - planar Connes-Kreimer antipode,
 - planar pruning,
 - cosubstitution.
-}
module Butcher.Planar (
    PlanarTree (..),
    magProduct,
    magLeft,
    magRight,
    magRoot,
    planarFactorial,
    shuffleCross,
    prune,
    planarAntipodeCK,
    cosub,
    buildSyntacticTree,
) where

import Butcher.Tree as T
import Core.Algebra
import Core.GradedList
import Core.Output
import Core.SyntacticTree
import Core.VectorSpace

{- $setup
>>> :set -XLambdaCase

>>> import Control.Monad.State
>>> import Core.SyntacticTree

  Integer Tree From Brackets
>>> itfb str = fromBrackets str :: PlanarTree Integer

  Integer Forest From Brackets
>>> iffb str = fromBrackets str :: [PlanarTree Integer]

  Leaves for testing @SyntacticTree@ functions:
>>> l1 = Leaf [PT 1 []]
>>> l2 = Leaf [PT 2 []]
>>> l3 = Leaf [PT 3 []]
>>> l4 = Leaf [PT 4 []]
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

{- |
  @PlanarTree@ is an instance of @IsTree@ and inherits all the relevant
  functions defined in @Tree@ module. It is the primary example of a tree
  and, therefore, we test the functionality of functions defined on @IsTree@
  using @PlanarTree@.

  Examples for @toBracketsWith@ and @fromBrackets@:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBracketsWith f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets "(1)[(2),3[04,05],(6)]" :: PlanarTree Integer
1[2,3[4,5],6]

  Examples for @parseTree@:

>>> evalState (parseTree read) "1[2]" :: PlanarTree Integer
1[2]

  Examples for @parseForest@:

>>> evalState (parseForest read) "1[2],3[4,5[6]],7" :: [PlanarTree Integer]
[1[2],3[4,5[6]],7]

  Examples for @graft@:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> graft f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5

  Examples for @grossmanLarson@:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> grossmanLarson f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5

  Examples for @syn@:

>>> f = [PT 1 [PT 2 [], PT 3 []], PT 4 []]
>>> syn f
concat(graft(concat([2],[3]),[1]),[4])

  Examples for @compose@:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> compose l1 [l3, l4] st
Just graft([3],graft([2],[4]))
>>> compose l1 [l3] st
Nothing
>>> compose l1 [l3, l4, l4] st
Nothing

  Examples for @symmetricCompose@:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> symmetricCompose l1 [l3, l4] st
(1 *^ graft([3],graft([2],[4])) + 1 *^ graft([4],graft([2],[3])))_3
>>> symmetricCompose l1 [l3] st
_0
>>> symmetricCompose l1 [l3, l4, l4] st
_0

  Examples for @eval@:

>>> st = Node graftOp [l1, Node graftOp [l2, l1]]
>>> v = symmetricCompose l1 [l3, l4] st
>>> eval st
(1 *^ [1[2[1]]] + 1 *^ [1[1,2]])_3
>>> linearGraded eval v
(1 *^ [4[2[3]]] + 1 *^ [4[3,2]] + 1 *^ [3[2[4]]] + 1 *^ [3[4,2]])_3

  Examples for @substitute@:

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
instance (Graded d) => IsTree (PlanarTree d) where
    root = planarRoot
    branches = planarBranches

    buildTree = PT

instance (Graded d) => HasBracketNotation (PlanarTree d) where
    toBracketsWith = treeToBracketsWith
    fromBracketsWith = treeFromBracketsWith

instance (Show d, Graded d) => Show (PlanarTree d) where
    show = toBrackets

instance (Show d, Graded d) => Texifiable (PlanarTree d) where
    texify = T.treeTexify

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

---------------------------------------------------------------------

-- * Magmatic product and related functions

---------------------------------------------------------------------

{- |
  Given two planar forests @f1@ and @f2@, the magmatic product of @f1@ and @f2@
  is the planar forest obtained by concatenation of @f1@ and the tree obtained by
  grafting all trees in @f2@ to a new root decorated by @c@.

Examples:

>>> f1 = iffb "1[2],3"
>>> f2 = iffb "4,5[6]"
>>> magProduct 7 f1 f2
[1[2],3,7[4,5[6]]]
-}
magProduct :: (IsTree t) => Decoration t -> [t] -> [t] -> [t]
magProduct c f1 f2 = f1 ++ [buildTree c f2]

{- |
  Every planar forest can be uniquely decomposed into a left part, a right part,
  and a root decoration.

Examples:

>>> magLeft $ iffb "1[2,3],4[5,6]"
[1[2,3]]
>>> magRight $ iffb "1[2,3],4[5,6]"
[5,6]
>>> magRoot $ iffb "1[2,3],4[5,6]"
4
-}
magLeft :: [t] -> [t]
magLeft = init

magRight :: (IsTree t) => [t] -> [t]
magRight = branches . last

magRoot :: (IsTree t) => [t] -> Decoration t
magRoot = T.root . last

{- |
  Planar factorial which is the coefficient map for the Lie-Butcher series
  of the exact solution.

See Equation 47 in
    Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Examples:

>>> f = iffb "1[2,3[4]]"
>>> planarFactorial f
12
-}
planarFactorial :: (IsTree t) => [t] -> Integer
planarFactorial [] = 1
planarFactorial f = grading f * planarFactorial (magLeft f) * planarFactorial (magRight f)

{- |
  A product on the tensor algebra of planar forests. Applies shuffle product
  to the left parts and magmatic product to the right parts. Used internally
  in the implementation of the Connes-Kreimer coproduct and the pruning formula.
-}
shuffleCross
    :: ( IsTree t
       , IsVector t
       )
    => Decoration t
    -> ([t], [t])
    -> ([t], [t])
    -> Vector (VectorScalar t) ([t], [t])
shuffleCross c (f11, f12) (f21, f22) = bilinear (,) (shuffle f11 f21) (vector $ magProduct c f12 f22)

{- |
  Planar Connes-Kreimer coproduct dual to the Grossman-Larson product.

See Equations 66 and 67 in
    Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Examples:

>>> f = iffb "1[2,3[4]]"
>>> connesKreimer f
(1 *^ ([1[2,3[4]]],[]) + 1 *^ ([2,3[4]],[1]) + 1 *^ ([2,4],[1[3]]) + 1 *^ ([4,2],[1[3]]) + 1 *^ ([4],[1[2,3]]) + 1 *^ ([2],[1[3[4]]]) + 1 *^ ([],[1[2,3[4]]]))_4
-}
instance (IsTree t, IsVector t) => CanConnesKreimer [t] where
    connesKreimer [] = vector ([], [])
    connesKreimer f = vector (f, []) + bilinear (shuffleCross c) (connesKreimer $ magLeft f) (connesKreimer $ magRight f)
      where
        c = magRoot f

{- |
  Planar Connes-Kreimer antipode.

See Equation 71 in
    Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Examples:

>>> f = iffb "1[1,1[1]]"
>>> planarAntipodeCK f
(12 *^ [1,1,1,1] + -2 *^ [1,1,1[1]] + -3 *^ [1,1[1],1] + -4 *^ [1[1],1,1] + 1 *^ [1,1[1,1]] + 1 *^ [1[1,1],1] + 1 *^ [1,1[1[1]]] + 1 *^ [1[1[1]],1] + -1 *^ [1[1,1[1]]])_4
-}
planarAntipodeCK
    :: ( IsTree t
       , IsVector t
       )
    => [t] -> Vector (VectorScalar t) [t]
planarAntipodeCK [] = vector []
planarAntipodeCK f =
    scale (-1) $
        linear (uncurry shuffle) $
            linear planarAntipodeCKleft $
                bilinear
                    (shuffleCross c)
                    (connesKreimer $ magLeft f)
                    (connesKreimer $ magRight f)
  where
    c = magRoot f
    planarAntipodeCKleft (f11, f12) = linear (,f12) $ planarAntipodeCK f11

{- |
  Planar pruning coproduct dual to the grafting product.

See Equations 68 and 69 in
    Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Examples:

>>> f = iffb "1[2,3[4]]"
>>> prune f
(1 *^ ([2,3[4]],[1]) + 1 *^ ([2,4],[1[3]]) + 1 *^ ([4,2],[1[3]]) + 1 *^ ([4],[1[2,3]]) + 1 *^ ([2],[1[3[4]]]) + 1 *^ ([],[1[2,3[4]]]))_4
-}
prune
    :: ( IsTree t
       , IsVector t
       )
    => [t] -> Vector (VectorScalar t) ([t], [t])
prune [] = vector ([], [])
prune f = bilinear (shuffleCross c) (prune $ magLeft f) (connesKreimer $ magRight f)
  where
    c = magRoot f

{- |
  Cosubstitution.

(!!!) The functional @a@ is assumed to satisfy
        @a c [] = 0@ and @a c (shuffle f1 f2) = 0@.

See Equation 79 in
    Munthe-Kaas, H. Z., & Føllesdal, K. K. (2018).
    Lie–Butcher Series, Geometry, Algebra and Computation.
    https://doi.org/10.1007/978-3-030-01397-4_3

Examples:

>>> f = iffb "1[1,1[1]]"
>>> a _ = \case [t] -> grading t; _ -> 0
>>> cosub [1] a f
(4 *^ [1])_1 + (6 *^ [1[1]])_2 + (6 *^ [1[1,1]])_3 + (1 *^ [1[1,1[1]]])_4
-}
cosub
    :: ( IsTree t
       , IsVector t
       )
    => [Decoration t]
    -> (Decoration t -> [t] -> VectorScalar t)
    -> [t]
    -> Vector (VectorScalar t) [t]
cosub _ _ [] = vector []
cosub cs a f = sum $ map (\c -> linear (perDecompTerm c) $ linear perDeconTerm $ deconcatenate' f) cs
  where
    perDeconTerm (f1, f2) =
        linear (\(f21, f22) -> 1 *^ ((f1, f21), f22)) $
            prune f2
    perDecompTerm c ((f1, f21), f22) =
        scale (a' c f22) $
            bilinear (magProduct c) (cosub cs a f1) (cosub cs a f21)
    a' _ [] = 0
    a' c f' = a c f'
    deconcatenate' = linear removeTerm . deconcatenate
      where
        removeTerm (_, []) = Empty
        removeTerm term = vector term

{- |
  We define magmatic product operation and build the corresponding syntactic tree for it.
  This is used for experimantation purposes only.
-}
magProductOp
    :: ( IsTree t
       , IsVector t
       , Show (Decoration t)
       )
    => Decoration t -> Operation [t]
magProductOp c = Op
    ("magprod[" ++ show c ++ "]")
    ("$\\times_" ++ show c ++ "$")
    2
    $ \case
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
