{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : RootedTree
Description : Planar and non-planar trees, forests, and their grafting and substitution.
Copyright   : (c) University of Geneva, 2024
License     : BSD-3
Maintainer  : Eugen Bronasco (ebronasco@gmail.com)
Stability   : experimental

Implementation of the post-Lie algebra of planar trees and
pre-Lie algebra of non-planar trees.
-}
module Core.Parse (
    IsDecorated (..),
    IsTree (..),
    HasBracketNotation (..),
    parseTree,
    parseDecoration,
    parseForest,
) where

import Data.List (intercalate)
import Control.Monad.State
import qualified Data.MultiSet as MS

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
    toBrackets :: (Decoration t -> String) -> t -> String

    -- | Convert a string to a tree using bracket notation.
    fromBrackets :: (String -> Decoration t) -> String -> t

class (IsDecorated t) => IsTree t where
    root :: t -> Decoration t

    children :: t -> [t]

    buildTree :: Decoration t -> [t] -> t

instance (IsTree t, HasBracketNotation t) => HasBracketNotation [t] where
    toBrackets f = intercalate "," . map (toBrackets f)
    fromBrackets decFromStr = evalState (parseForest decFromStr)

instance (Ord t, IsTree t, HasBracketNotation t) => HasBracketNotation (MS.MultiSet t) where
    toBrackets f = intercalate "," . map (toBrackets f) . MS.toList
    fromBrackets decFromStr = MS.fromList . evalState (parseForest decFromStr)

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
    let (dec', str') = span (`notElem` ",[]") str
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


