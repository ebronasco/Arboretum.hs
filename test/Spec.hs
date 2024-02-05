import Test.DocTest
import Test.QuickCheck

main = doctest ["-isrc", "src/Symbolics.hs", "src/RootedTree.hs", "src/GradedList.hs"]
