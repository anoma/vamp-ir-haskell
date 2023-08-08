import qualified ParserSpec
import qualified ThreeACSpec
import qualified FlattenSpec

import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "InferAssignment Tests" ParserSpec.parserSpec
  describe "ThreeAC Inference Tests" ThreeACSpec.inferAssignmentSpec
  describe "Flatten Tests" FlattenSpec.flattenSpec
