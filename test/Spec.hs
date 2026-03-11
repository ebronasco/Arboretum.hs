import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/Core/Algebra.hs"
        , "src/Core/VectorSpace.hs"
        , "src/Core/GradedList.hs"
        , "src/Core/SyntacticTree.hs"
        , "src/Butcher/NonPlanar.hs"
        , "src/Butcher/Planar.hs"
        , "src/Butcher/Aromatic.hs"
        , "src/Butcher/Graph.hs"
        , "src/Butcher/Series.hs"
        , "src/Butcher/Tree.hs"
        ]
