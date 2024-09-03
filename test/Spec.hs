import Test.DocTest

main :: IO ()
main =
    doctest
        [ "-isrc"
        , "src/Symbolics.hs"
        , "src/GradedList.hs"
        ]
