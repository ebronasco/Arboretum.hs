module RootedTree (
    PRTree (..),
    vertices,
    graft,
    graftTo,
) where

import Data.List (intersperse)
import GradedList
import Output
import Symbolics

-- Planar rooted tree
data PRTree a = PRTree
    { root :: a
    , children :: [PRTree a]
    }
    deriving (Eq)

instance (Show a) => Show (PRTree a) where
    show (PRTree r xs) =
        show r
            ++ ( case xs of
                    [] -> ""
                    _ -> show xs
               )

instance (Texifiable a) => Texifiable (PRTree a) where
    texify t = "\\forest{" ++ (texify_ t) ++ "}"

texify_ (PRTree r xs) =
    "i_"
        ++ (texify r)
        ++ ( case xs of
                [] -> ""
                _ -> "[" ++ (concat $ intersperse "," $ map texify_ xs) ++ "]"
           )

instance (Basis a) => Graded (PRTree a) where
    grading (PRTree r xs) = (grading r) + sum (map grading xs)

instance (Basis a) => Basis (PRTree a)

vertices :: (Basis a) => PRTree a -> [a]
vertices (PRTree x xs) = x : concatMap vertices xs

graft :: (Basis a) => PRTree a -> PRTree a -> VectorSpace Integer (PRTree a)
graft t1 t2 = basisVector $ map (graftTo t1 t2) $ vertices t2

graftTo :: (Basis a) => PRTree a -> PRTree a -> a -> PRTree a
graftTo t1 (PRTree r xs) v
    | v == r = PRTree v (t1 : xs)
    | otherwise = PRTree r (map (\x -> graftTo t1 x v) xs)
