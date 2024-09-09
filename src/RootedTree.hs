{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
    IsDecorated (..),
    IsTree (..),
    HasBracketNotation (..),
    parseForest,
    PlanarTree (..),
    Tree (..),
    Planarable,
    Planar,
    nonplanar,
    planar,
    Graftable,
    graft,
    gl,
) where

import Control.Monad.State
import Data.List (intercalate)
import qualified Data.MultiSet as MS
import GradedList
import Output
import Symbolics

{- $setup
  Integer Tree From Brackets
>>> itfb str = fromBrackets read str :: Tree Integer

  Non-Planar Integer Tree From Brackets
>>> npitfb str = fromBrackets read str :: Tree Integer
-}

class IsDecorated a where
    type Decoration a

instance (IsDecorated t) => IsDecorated [t] where
    type Decoration [t] = Decoration t

instance (IsDecorated t) => IsDecorated (MS.MultiSet t) where
    type Decoration (MS.MultiSet t) = Decoration t

instance
    ( IsDecorated t1
    , IsDecorated t2
    , Decoration t1 ~ Decoration t2
    )
    => IsDecorated (t1, t2)
    where
    type Decoration (t1, t2) = Decoration t1

class (IsDecorated t) => IsTree t where

    root :: t -> Decoration t

    children :: t -> [t]

    buildTree :: Decoration t -> [t] -> t

class (IsDecorated t) => HasBracketNotation t where
    -- | Convert a tree to a string using bracket notation.
    -- The first argument is a function that converts the decoration
    -- to a string.
    toBrackets :: (Decoration t -> String) -> t -> String

    -- | Convert a string to a tree using bracket notation.
    fromBrackets :: (String -> Decoration t) -> String -> t

instance (IsTree t, HasBracketNotation t) => HasBracketNotation [t] where
    toBrackets f = intercalate "," . map (toBrackets f)
    fromBrackets decFromStr = evalState (parseForest decFromStr)

instance (Ord t, IsTree t, HasBracketNotation t) => HasBracketNotation (MS.MultiSet t) where
    toBrackets f = intercalate "," . map (toBrackets f) . MS.toList
    fromBrackets decFromStr = MS.fromList . evalState (parseForest decFromStr)

{- 
  The functions @parseTree@, @parseDecoration@, and @parseForest@ are
  used to parse a string into a tree or forest using the bracket
  notation. They are placed outside the instance definition to allow
  other instances to use them.

Examples:

>>> evalState (parseTree read) "1[2]"
1[2]
>>> evalState (parseForest read) "1[2],3[4,5[6]],7"
[1[2],3[4,5[6]],7]
>>> evalState (parseDecoration read) "1234["
1234
-}
parseTree :: (IsTree t) => (String -> Decoration t) -> State String t
parseTree decFromStr = do
    dec <- parseDecoration decFromStr

    str <- get

    case str of
        [] -> return $ buildTree dec []
        ('[' : str') -> do
            put str'
            chldrn <- parseForest decFromStr
            return $ buildTree dec chldrn
        (',' : str') -> do
            put str'
            return $ buildTree dec []
        (']' : str') -> do
            put str'
            return $ buildTree dec []
        _ -> error "fromBrackets: invalid input"

parseDecoration :: (String -> d) -> State String d
parseDecoration decFromStr = do
    str <- get
    let (dec', str') = span (\x -> x `notElem` ",[]") str
    case dec' of
        [] -> error "fromBrackets: empty decoration"
        _ -> do
            put str'
            return $ decFromStr dec'

parseForest :: (IsTree t) => (String -> Decoration t) -> State String [t]
parseForest decFromStr = do
    str <- get
    case str of
        [] -> return []
        (']' : str') -> do
            put str'
            return []
        (',' : str') -> do
            put str'
            return []
        _ -> do 
            chld <- parseTree decFromStr
            chldrn <- parseForest decFromStr
            return $ chld : chldrn

---------------------------------------------------------------------

-- * Planar trees

---------------------------------------------------------------------

{- | Planar trees are represented as a tree with a root and a list of
children which are planar trees themselves.
-}
data PlanarTree d = PT
    { planarRoot :: d
    , planarChildren :: [PlanarTree d]
    }
    deriving (Eq)

instance IsDecorated (PlanarTree d) where
    type Decoration (PlanarTree d) = d

instance IsTree (PlanarTree d) where
    root = planarRoot
    children = planarChildren

    buildTree = PT

{- |
  Every tree can be written and constructed from a string using
  the bracket notation.

Example:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBrackets f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets read "(1)[(2),3[04,05],(6)]" :: Tree Integer
1[2,3[4,5],6]
-}
instance HasBracketNotation (PlanarTree d) where
    toBrackets f t =
        f (root t)
            ++ ( case children t of
                    [] -> ""
                    _ -> "[" ++ intercalate "," (map (toBrackets f) (children t)) ++ "]"
               )

    fromBrackets decFromStr = evalState (parseTree decFromStr)



{- |
  LaTeX notation for planar trees using @planarforest.py@ TeX package.

Example:

>>> texify $ itfb "1[2,3]"
"\\forest{i_1[i_2,i_3]}"
-}
instance (Show d) => Texifiable (PlanarTree d) where
    texifyID _ = "PlanarTree"
    texify t = "\\forest{" ++ toBrackets wrap t ++ "}"
      where
        wrap r = "i_" ++ filter (/= '"') (show r)

instance (Show d) => Show (PlanarTree d) where
    show = toBrackets show

-- | Planar trees are vectors with integer coefficients.
instance (Eq d, Graded d) => IsVector (PlanarTree d) where
    type VectorScalar (PlanarTree d) = Integer
    type VectorBasis (PlanarTree d) = PlanarTree d

    vector = vector . (1 *^)

{- |
  Grading of a planar tree is the sum of gradings of the nodes.

Example:

>>> grading $ itfb "1[2,34]"
4

Note: the grading of an integer is the number of digits with @0@ having grading @0@.
-}
instance (Graded d) => Graded (PlanarTree d) where
    grading (PT r xs) = grading r + sum (map grading xs)

---------------------------------------------------------------------

-- * Non-planar trees

---------------------------------------------------------------------

{- | Non-planar trees are represented as a tree with a root and a
multiset of children which are non-planar trees themselves.
-}
data Tree d = T
    { nonplanarRoot :: d
    , nonplanarChildren :: MS.MultiSet (Tree d)
    }
    deriving (Eq)

instance IsDecorated (Tree d) where
    type Decoration (Tree d) = d

instance (Ord d) => IsTree (Tree d) where
    root = nonplanarRoot
    children = MS.toAscList . nonplanarChildren

    buildTree r = T r . MS.fromList

{- |
  Every tree can be written and constructed from a string using
  the bracket notation.

Example:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBrackets f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets read "(1)[(2),3[04,05],(6)]" :: Tree Integer
1[2,3[4,5],6]
-}
instance (Ord d) => HasBracketNotation (Tree d) where
    toBrackets f t =
        f (root t)
            ++ ( case children t of
                    [] -> ""
                    _ -> "[" ++ intercalate "," (map (toBrackets f) (children t)) ++ "]"
               )

    fromBrackets decFromStr = evalState (parseTree decFromStr)

{- |
  LaTeX notation for trees using @planarforest.py@ TeX package.

Example:

>>> texify $ itfb "1[2,3]"
"\\forest{i_1[i_2,i_3]}"
-}
instance (Show d, Ord d) => Texifiable (Tree d) where
    texifyID _ = "Tree"
    texify = texify . planar

instance (Show d, Ord d) => Show (Tree d) where
    show = toBrackets show

instance (Eq d, Ord d, Graded d) => IsVector (Tree d) where
    type VectorScalar (Tree d) = Integer
    type VectorBasis (Tree d) = Tree d

    vector = vector . (1 *^)

{- |
  Order on decorations induces an order on trees where we first
  compare the root decorations and then the children according to
  their order.

Example:

>>> compare (npitfb "1") (npitfb "2")
LT
>>> compare (npitfb "1") (npitfb "1[2,3]")
LT
>>> compare (npitfb "1[2]") (npitfb "1[3]")
LT
>>> compare (npitfb "1[2]") (npitfb "1[2]")
EQ
>>> compare (npitfb "1[2,4]") (npitfb "1[2,3]")
GT
-}
instance (Ord d) => Ord (Tree d) where
    compare (T r1 c1) (T r2 c2) = compare (r1, c1) (r2, c2)

instance (Ord d, Graded d) => Graded (Tree d) where
    grading = grading . planar

---------------------------------------------------------------------

-- * Moving between planar and non-planar trees

---------------------------------------------------------------------

class Planarable t where
    type Planar t

    planar :: t -> Planar t
    nonplanar :: Planar t -> t

instance (Ord d) => Planarable (Tree d) where
    type Planar (Tree d) = PlanarTree d

    -- \| Choose a canonical planar representation of a non-planar
    -- tree.
    --
    --    Example:
    --
    --    >>> planar $ npitfb "1[2,3]"
    --    1[2,3]
    --
    planar (T r xs) = PT r (planar xs)

    -- \| Forget the order of children in a planar tree.
    --
    --    Example:
    --
    --    >>> a =  nonplanar $ itfb "1[2,3]"
    --    >>> b =  nonplanar $ itfb "1[3,2]"
    --    >>> a == b
    --    True
    --
    nonplanar (PT r xs) = T r (nonplanar xs)

instance (Ord t, Planarable t) => Planarable (MS.MultiSet t) where
    type Planar (MS.MultiSet t) = [Planar t]

    -- \| Choose a canonical planar representation of a non-planar
    -- forest.
    --
    --    Example:
    --
    --    >>> planar $ MS.fromList [npitfb "1[2,3]", npitfb "4"]
    --    [1[2,3],4]
    --
    planar = map planar . MS.toList

    -- \| Forget the order of trees and children in a planar forest.
    --
    --    Example:
    --
    --    >>> a = nonplanar $ [itfb "1[2,3]", itfb "4"]
    --    >>> b = nonplanar $ [itfb "4", itfb "1[3,2]"]
    --    >>> a == b
    --    True
    --
    nonplanar = MS.fromList . map nonplanar

---------------------------------------------------------------------

-- * Grafting product

---------------------------------------------------------------------

class (IsVector a) => Graftable a where
    graft :: a -> a -> Vector (VectorScalar a) (VectorBasis a)

{- |
  Grafting of two planar forests using the @deshuffleCoproduct@
  function that splits @f1@ into subforests in all possible ways.

Example:

>>> f1 = [itfb "1[2]"]
>>> f2 = [itfb "3", itfb "4[5]"]
>>> graft f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5
-}
instance
    ( IsTree t
    , IsVector t
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Eq (Decoration t)
    , Graded (Decoration t)
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
    , Num (VectorScalar t)
    , Eq (VectorScalar t)
    , Eq t
    , Graded t
    , Ord t
    , Eq (Decoration t)
    , Graded (Decoration t)
    , Ord (Decoration t)
    )
    => Graftable (MS.MultiSet t)
    where
    graft f1 f2 = linear MS.fromList $ graft (MS.toList f1) (MS.toList f2)

{- |
  Grossman-Larson product of two forests.

Example:

>>> f1 = [itfb "1[2]"]
>>> f2 = [itfb "3", itfb "4[5]"]
>>> gl f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5
-}
gl
    :: ( IsTree t
       , IsVector t
       , Num (VectorScalar t)
       , Eq (VectorScalar t)
       , Eq t
       , Graded t
       , Eq (Decoration t)
       , Graded (Decoration t)
       )
    => [t]
    -> [t]
    -> Vector (VectorScalar t) [t]
gl f1 f2 = linear perCoproductTerm $ deshuffleCoproduct f1
  where
    perCoproductTerm (f11, f12) = vector f11 * graft f12 f2
