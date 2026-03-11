{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -w #-}

import Control.Monad.State.Lazy
import Data.MultiSet as MS

import Core.GradedList
import Core.Output
import Core.SyntacticTree
import Core.VectorSpace
import Core.Algebra
import Butcher.Aromatic
import Butcher.Graph
import Butcher.NonPlanar
import Butcher.Planar
import Butcher.Series

main :: IO ()
main = do
    putStrLn "Type \":l examples/[ExampleName].hs \" to load and example and \":main\" to run it."
    putStrLn ""
    putStrLn "Available examples:"
    putStrLn "  - Graph"
    putStrLn "  - ConcatDeshuffle"
    putStrLn "  - ShuffleDeconcat"
    putStrLn "  - PlanarGrossmanLarson"
    putStrLn "  - PlanarConnesKreimer"
    putStrLn "  - NonplanarGrossmanLarson"
    putStrLn "  - NonplanarConnesKreimer"
    putStrLn "  - Cosubstitution"
    putStrLn ""
    putStrLn ""
    putStrLn "Type \":quit\" to exit."
