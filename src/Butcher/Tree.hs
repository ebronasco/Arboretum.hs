{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : Buther.Tree
Description : Define decorated trees as a class and along with their bracket notation.
Copyright   : (c) Chalmers University of Technology and Gothenburg University, 2025
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental
-}
module Butcher.Tree (
    IsDecorated (..),
    IsTree (..),
    HasBracketNotation (..),
    treeToBracketsWith,
    treeFromBracketsWith,
    treeTexify,
    parseTree,
    parseForest,
    parseDecoration,
    CanGraft (..),
    CanGrossmanLarson (..),
    CanConnesKreimer (..),
    graftOp,
    concatOp,
) where

import Data.List (intercalate)
import Control.Monad.State
import qualified Data.MultiSet as MS
import Core.VectorSpace
import Core.SyntacticTree
import Core.GradedList
import Core.Algebra

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

class (IsDecorated t) => HasBracketNotation t where
    {- | Convert a tree to a string using bracket notation.
    The first argument is a function that converts the decoration
    to a string.
    -}
    toBracketsWith :: (Decoration t -> String) -> t -> String

    toBrackets :: (Show (Decoration t)) => t -> String
    toBrackets = toBracketsWith show

    -- | Convert a string to a tree using bracket notation.
    fromBracketsWith :: (String -> Decoration t) -> String -> t

    fromBrackets :: (Read (Decoration t)) => String -> t
    fromBrackets = fromBracketsWith read

class (IsDecorated t, Graded t) => IsTree t where
    root :: t -> Decoration t

    branches :: t -> [t]

    buildTree :: Decoration t -> [t] -> t

{- |
  Every tree can be written and constructed from a string using
  the bracket notation.

Example:

>>> f r = "(" ++ (show r) ++ ")"
>>> toBracketsWith f $ itfb "1[2,3]"
"(1)[(2),(3)]"
>>> fromBrackets "(1)[(2),3[04,05],(6)]" :: Tree Integer
1[2,3[4,5],6]
-}
treeToBracketsWith :: (IsTree t) => (Decoration t -> String) -> t -> String
treeToBracketsWith f t =
        f (root t)
            ++ ( case branches t of
                    [] -> ""
                    _ -> "[" ++ intercalate "," (map (treeToBracketsWith f) (branches t)) ++ "]"
               )

treeFromBracketsWith :: (IsTree t) => (String -> Decoration t) -> String -> t
treeFromBracketsWith decFromStr str = evalState (parseTree decFromStr) str

treeTexify :: (Show (Decoration t), IsTree t) => t -> String
treeTexify t = "\\forest{" ++ treeToBracketsWith wrap t ++ "}"
  where
    wrap r = "i_" ++ filter (/= '"') (show r)

instance (IsTree t, HasBracketNotation t) => HasBracketNotation [t] where
    toBracketsWith strFromDec = intercalate [','] . map (toBracketsWith strFromDec)
    fromBracketsWith decFromStr = evalState (parseForest decFromStr)

instance (Ord t, IsTree t, HasBracketNotation t) => HasBracketNotation (MS.MultiSet t) where
    toBracketsWith strFromDec = intercalate [','] . map (toBracketsWith strFromDec) . MS.toList
    fromBracketsWith decFromStr = MS.fromList . evalState (parseForest decFromStr)



{- |
  The function @parseTree@ is used to parse a string into a tree
  using the bracket notation.

Examples:

>>> evalState (parseTree read) "1[2]" :: PlanarTree Integer
1[2]
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

{- |
  The function @parseDecoration@ is used to parse a string as a
  decoration using the bracket notation.

Examples:

>>> evalState (parseDecoration read) "1234[" :: Integer
1234
-}
parseDecoration :: (String -> d) -> State String d
parseDecoration decFromStr = do
    str <- get
    let (dec', str') = span (`notElem` [',','[',']']) str
    case dec' of
        [] -> error "fromBrackets: empty decoration"
        _ -> do
            put str'
            return $ decFromStr dec'

{- |
  The function @parseForest@ is used to parse a string into a forest
  using the bracket notation.

Examples:

>>> evalState (parseForest read) "1[2],3[4,5[6]],7" :: [PlanarTree Integer]
[1[2],3[4,5[6]],7]
-}
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

-- * Grafting

---------------------------------------------------------------------

class (IsVector a) => CanGraft a where
    graft :: a -> a -> Vector (VectorScalar a) (VectorBasis a)

{- |
  Grafting of two planar forests using the @deshuffleCoproduct@
  function that splits @f1@ into subforests in all possible ways.

Example:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> graft f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]])_5
-}
instance
    ( IsTree t
    , IsVector t
    )
    => CanGraft [t]
    where
    graft [] [] = vector []
    graft _ [] = vector Zero
    graft [] f2 = vector f2
    graft f [t] = linear ((: []) . buildTree (root t)) $ grossmanLarson f $ branches t
    graft f1 (t : f2) =
        linear perCoproductTerm $ deshuffle f1
      where
        perCoproductTerm (f11, f12) = graft f11 [t] * graft f12 f2

instance
    ( IsTree t
    , IsVector t
    , Ord t
    )
    => CanGraft (MS.MultiSet t)
    where
    graft f1 f2 = linear MS.fromList $ graft (MS.toList f1) (MS.toList f2)


class (IsVector a) => CanGrossmanLarson a where
    grossmanLarson :: a -> a -> Vector (VectorScalar a) (VectorBasis a)

{- |
  Grossman-Larson product of two forests.

Example:

>>> f1 = iffb "1[2]"
>>> f2 = iffb "3,4[5]"
>>> grossmanLarson f1 f2
(1 *^ [3,4[5[1[2]]]] + 1 *^ [3,4[1[2],5]] + 1 *^ [3[1[2]],4[5]] + 1 *^ [1[2],3,4[5]])_5
-}
instance 
    ( IsTree t
    , IsVector t
    )
    => CanGrossmanLarson [t]
    where
    grossmanLarson f1 f2 = linear perCoproductTerm $ deshuffle f1
      where
        perCoproductTerm (f11, f12) = vector f11 * graft f12 f2

instance
    ( IsTree t
    , IsVector t
    , Ord t
    )
    => CanGrossmanLarson (MS.MultiSet t)
    where
    grossmanLarson f1 f2 = linear MS.fromList $ grossmanLarson (MS.toList f1) (MS.toList f2)


class (IsVector a) => CanConnesKreimer a where
    connesKreimer :: a -> Vector (VectorScalar a) (VectorBasis a, VectorBasis a)



---------------------------------------------------------------------

-- * Substitution

---------------------------------------------------------------------

-- | Grafting operation.
graftOp :: (IsVector a, CanGraft a) => Operation a
graftOp = Op "graft" "$\\curvearrowright$" 2 $
    \case
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
    )
    => HasSyntacticTree [t]
    where
    syn [t] = case branches t of
        [] -> Leaf [t]
        _ -> Node graftOp [syn (branches t), Leaf [buildTree (root t) []]]
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
    , Ord t
    )
    => HasSyntacticTree (MS.MultiSet t)
    where
    syn ts = case MS.toList ts of
        [t] -> case branches t of
            [] -> Leaf $ MS.singleton t
            _ -> Node graftOp [syn (MS.fromList $ branches t), Leaf $ MS.singleton $ buildTree (root t) []]
        ts' -> Node concatOp $ map (syn . MS.singleton) ts'
