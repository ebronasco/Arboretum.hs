import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/Core/Symbolics.hs"
        , "src/Core/GradedList.hs"
        , "src/Core/SyntacticTree.hs"
        , "src/Butcher/NonPlanar.hs"
        , "src/Butcher/Aromatic.hs"
        , "src/Butcher/Graph.hs"
        ]
