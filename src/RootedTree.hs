{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : RootedTree
Description : Planar and non-planar trees, forests, and their grafting and substitution.
Copyright   : (c) University of Geneva, 2024
License     : MIT
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the post-Lie algebra of planar trees and
pre-Lie algebra of non-planar trees.
-}
module RootedTree (
    IsTree (..),
    PlanarTree (..),
    Tree (..),
    Planarable,
    Planar,
    nonplanar,
    planar,
    Graftable,
    graft,
    gl,
    Operation (..),
    graftOp,
    concatOp,
    SyntacticTree (..),
    syntacticToPlanar,
    compose,
    symmetricCompose,
) where

import Data.List (intercalate, permutations)
import Data.Maybe (fromJust)
import qualified Data.MultiSet as MS
import GradedList
import Output
import Symbolics

-- * Tree

class IsTree t where
    type TreeDecoration t

    root :: t -> TreeDecoration t
    children :: t -> [t]

    buildTree :: TreeDecoration t -> [t] -> t

-- ** Planar trees

-- | Planar trees are represented as a tree with a root and a list of children which are planar trees themselves.
data PlanarTree d = PT
    { planarRoot :: d
    , planarChildren :: [PlanarTree d]
    }
    deriving (Eq)

instance IsTree (PlanarTree d) where
    type TreeDecoration (PlanarTree d) = d

    root = planarRoot
    children = planarChildren

    buildTree = PT

{- | Represent planar trees as strings using bracket notation.

Example:

>>> PT 1 [PT 2 [], PT 3 []]
1[2,3]
-}
instance (Show d) => Show (PlanarTree d) where
    show (PT r xs) =
        show r
            ++ ( case xs of
                    [] -> ""
                    _ -> show xs
               )

-- | Planar trees are vectors with integer coefficients.
instance (Eq d, Graded d) => IsVector (PlanarTree d) where
    type VectorScalar (PlanarTree d) = Integer
    type VectorBasis (PlanarTree d) = PlanarTree d

    vector = vector . (1 *^)

{- | LaTeX notation for planar trees using @planarforest.py@ TeX package.

Example:

>>> texify $ PT 1 [PT 2 [], PT 3 []]
"\\forest{i_1[i_2,i_3]}"
-}
instance (Show d, Texifiable d) => Texifiable (PlanarTree d) where
    texifyID _ = "PlanarTree"
    texify t = "\\forest{" ++ texify_ t ++ "}"
      where
        texify_ (PT r xs) =
            "i_"
                ++ (filter (/= '"') $ show r)
                ++ ( case xs of
                        [] -> ""
                        _ -> "[" ++ intercalate "," (map texify_ xs) ++ "]"
                   )

{- | Grading of a planar tree is the sum of gradings of the nodes.

Example:

>>> grading $ PT 1 [PT 2 [], PT 31 []]
4

Note that the grading of an integer is the number of digits with @0@ having grading @0@.
-}
instance (Graded d) => Graded (PlanarTree d) where
    grading (PT r xs) = grading r + sum (map grading xs)

-- ** Non-planar trees

-- | Non-planar trees are represented as a tree with a root and a multiset of children which are non-planar trees themselves.
data Tree d = T
    { nonplanarRoot :: d
    , nonplanarChildren :: MS.MultiSet (Tree d)
    }
    deriving (Eq)

instance (Ord d) => IsTree (Tree d) where
    type TreeDecoration (Tree d) = d

    root = nonplanarRoot
    children = MS.toAscList . nonplanarChildren

    buildTree r = T r . MS.fromList

instance (Eq d, Ord d, Graded d) => IsVector (Tree d) where
    type VectorScalar (Tree d) = Integer
    type VectorBasis (Tree d) = Tree d

    vector = vector . (1 *^)

instance (Ord d) => Ord (Tree d) where
    compare (T r1 c1) (T r2 c2) = compare (r1, c1) (r2, c2)

instance (Ord d, Graded d) => Graded (Tree d) where
    grading = grading . planar

instance (Ord d, Show d, Texifiable d) => Texifiable (Tree d) where
    texifyID _ = "Tree"
    texify = texify . planar

instance (Eq a, Texifiable a) => Texifiable (MS.MultiSet a) where
    texifyID _ = "MultiSet"
    texify = texify . MS.toList
    texifyDebug i j = texifyDebug i j . MS.toList

-- | Represent non-planar trees as strings using brace notation. Children are enclosed in curly braces.
instance (Show d) => Show (Tree d) where
    show (T r xs) =
        show r
            ++ ( case MS.toList xs of
                    [] -> ""
                    _ -> "{" ++ (tail . init . show . MS.toList) xs ++ "}"
               )

-- * Moving between planar and non-planar trees

class Planarable t where
    type Planar t

    planar :: t -> Planar t
    nonplanar :: Planar t -> t

instance (Ord d) => Planarable (Tree d) where
    type Planar (Tree d) = PlanarTree d

    -- \| Choose a canonical planar representation of a non-planar tree.
    --
    --    Example:
    --
    --    >>> planar $ T 1 (MS.fromList [T 2 MS.empty, T 3 MS.empty])
    --    1[2,3]
    --
    planar (T r xs) = PT r (planar xs)

    -- \| Forget the order of children in a planar tree.
    --
    --    Example:
    --
    --    >>> a =  nonplanar $ PT 1 [PT 2 [], PT 3 []]
    --    >>> b =  nonplanar $ PT 1 [PT 3 [], PT 2 []]
    --    >>> a == b
    --    True
    --
    nonplanar (PT r xs) = T r (nonplanar xs)

instance (Ord d) => Planarable (MS.MultiSet (Tree d)) where
    type Planar (MS.MultiSet (Tree d)) = [PlanarTree d]

    -- \| Choose a canonical planar representation of a non-planar forest.
    --
    --    Example:
    --
    --    >>> planar $ MS.fromList [T 1 (MS.fromList [T 2 MS.empty, T 3 MS.empty]), T 4 MS.empty]
    --    [1[2,3],4]
    --
    planar = map planar . MS.toList

    -- \| Forget the order of trees and children in a planar forest.
    --
    --    Example:
    --
    --    >>> a = nonplanar $ [PT 1 [PT 2 [], PT 3 []], PT 4 []]
    --    >>> b = nonplanar $ [PT 4 [], PT 1 [PT 3 [], PT 2 []]]
    --    >>> a == b
    --    True
    --
    nonplanar = MS.fromList . map nonplanar

-- * Grafting product

class (IsVector a) => Graftable a where
    graft :: a -> a -> Vector (VectorScalar a) (VectorBasis a)

{- | Grafting of two planar forests using the @deshuffleCoproduct@ function that splits @f1@ into subforests in all possible ways.

Example:

>>> graft [PT 1 [PT 2 []]] [PT 3 [], PT 4 [PT 5 []]]
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5
-}
instance
    ( IsTree t
    , IsVector t
    , Eq t
    , Graded t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    )
    => Graftable [t]
    where
    graft [] [] = vector []
    graft _ [] = vector Zero
    graft [] f2 = vector f2
    graft f [t] = linear ((: []) . buildTree (root t)) $ gl f $ children t
    graft f1 (t : f2) =
        linear perCoproductTerm $ deshuffleCoproduct f1
      where
        perCoproductTerm (f11, f12) = graft f11 [t] * graft f12 f2

instance
    ( IsTree t
    , IsVector t
    , Eq t
    , Graded t
    , Ord t
    , Eq (TreeDecoration t)
    , Graded (TreeDecoration t)
    , Ord (TreeDecoration t)
    )
    => Graftable (MS.MultiSet t)
    where
    graft f1 f2 = linear MS.fromList $ graft (MS.toList f1) (MS.toList f2)

{- | Grossman-Larson product of two forests.

Example:

>>> gl [PT 1 [PT 2 []]] [PT 3 [], PT 4 [PT 5 []]]
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5
-}
gl
    :: ( IsTree t
       , IsVector t
       , Eq t
       , Graded t
       , Eq (TreeDecoration t)
       , Graded (TreeDecoration t)
       )
    => [t]
    -> [t]
    -> Vector Integer [t]
gl f1 f2 = linear perCoproductTerm $ deshuffleCoproduct f1
  where
    perCoproductTerm (f11, f12) = vector f11 * graft f12 f2

-- * Substitution

data Operation a = Op
    { name :: String
    , tex :: String
    , arity :: Int
    , func :: [a] -> Vector (VectorScalar a) a
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
    syn :: a -> Vector (VectorScalar a) (SyntacticTree a)

eval :: SyntacticTree a -> Vector (VectorScalar a) (VectorBasis a)
eval (Leaf a) = vector a
eval (Node op as) = linear (func op) $ product $ map eval as

graftOp :: (IsVector a, Graftable a) => Operation a
graftOp = Op "graft" "$\\curvearrowright$" 2 $
    \ops -> case ops of
        [x, y] -> graft x y
        _ -> error "graftOp: arity"

concatOp :: (IsVector a, Monoid a) => Operation a
concatOp = Op "concat" "$\\cdot$" (-1) $
    \ops -> vector $ mconcat ops


