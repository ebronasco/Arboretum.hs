import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/Symbolics.hs"
        , "src/RootedTree.hs"
        , "src/GradedList.hs"
        , "src/Graph.hs"
        , "src/AromaticTree.hs"
        , "src/Substitution.hs"
        ]
