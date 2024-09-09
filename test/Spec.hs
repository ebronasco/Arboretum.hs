import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/Symbolics.hs"
        , "src/GradedList.hs"
        , "src/RootedTree.hs"
        , "src/SyntacticTree.hs"
        , "src/AromaticTree.hs"
        , "src/Graph.hs"
        ]
