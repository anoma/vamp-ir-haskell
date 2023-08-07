-- In Spec.hs
import qualified ParserSpec
import qualified ThreeACSpec

import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "InferAssignment Tests" ParserSpec.parserSpec
  describe "ThreeACEval Tests" ThreeACSpec.inferAssignmentSpec
