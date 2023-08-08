module ThreeACSpec where

import Test.Hspec
import qualified Data.Map as M
import Test.QuickCheck
import ThreeAddress

inferAssignmentSpec :: Spec
inferAssignmentSpec = describe "inferAssignment" $ do
    describe "EVC Inference" $ 
        testInference (\[(id1, _), (_, val2)] -> EVC (newVar id1) val2) [True, True] [False, False]
    describe "EVV Inference (1, with positive x)" $ 
        testInference (\[(id1, _), (id2, _)] -> EVV (Pos (newVar id1)) (newVar id2)) [True, True] [True, False]
    describe "EVV Inference (2, with positive x)" $ 
        testInference (\[(id1, _), (id2, _)] -> EVV (Pos (newVar id1)) (newVar id2)) [True, True] [False, True]
    describe "EVV Inference (1, with negative x)" $ 
        testInference (\[(id1, _), (id2, _)] -> EVV (Neg (newVar id1)) (newVar id2)) [True, True] [True, False]
    describe "EVV Inference (righy, with negative x)" $ 
        testInference (\[(id1, _), (id2, _)] -> EVV (Neg (newVar id1)) (newVar id2)) [True, True] [False, True]
    describe "AddVCV Inference (1)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> AddVCV (newVar id1) val2 (newVar id3)) [True, True, True] [True, False, False]
    describe "AddVCV Inference (2)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> AddVCV (newVar id1) val2 (newVar id3)) [True, True, True] [False, False, True]
    describe "AddCVV Inference (1)" $
        testInference (\[(id1, val1), (id2, _), (id3, _)] -> AddCVV val1 (newVar id2) (newVar id3)) [True, True, True] [False, True, False]
    describe "AddCVV Inference (2)" $
        testInference (\[(id1, val1), (id2, _), (id3, _)] -> AddCVV val1 (newVar id2) (newVar id3)) [True, True, True] [False, False, True]
    describe "AddVVV Inference (1, 2, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, True, False]
    describe "AddVVV Inference (1, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, False, True]
    describe "AddVVV Inference (2, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "AddVVV Inference (1, 2, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, True, False]
    describe "AddVVV Inference (1, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, False, True]
    describe "AddVVV Inference (2, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "MulCVV Inference (1)" $
        testInference (\[(id1, val1), (id2, _), (id3, _)] -> MulCVV val1 (newVar id2) (newVar id3)) [True, False, True] [False, True, False]
    describe "MulCVV Inference (2)" $
        testInference (\[(id1, val1), (id2, _), (id3, _)] -> MulCVV val1 (newVar id2) (newVar id3)) [True, True, False] [False, False, True]
    describe "MulVCV Inference (1)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> MulVCV (newVar id1) val2 (newVar id3)) [True, False, True] [True, False, False]
    describe "MulVCV Inference (2)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> MulVCV (newVar id1) val2 (newVar id3)) [True, True, True] [False, False, True]
    describe "MulVVV Inference (1, 2, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, False, True]
            [True, True, False]
    describe "MulVVV Inference (1, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "MulVVV Inference (2, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "MulVVV Inference (1, 2, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, False, True]
            [True, True, False]
    describe "MulVVV Inference (1, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "MulVVV Inference (2, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "DivCCV Inference" $
        testInference (\[(_, val1), (_, val2), (id3, _)] -> DivCCV val1 val2 (newVar id3)) [False, False, False] [False, False, False]
    describe "DivCVV Inference (1)" $
        testInference (\[(_, val1), (id2, _), (id3, _)] -> DivCVV val1 (newVar id2) (newVar id3)) [False, False, False] [False, True, False]
    describe "DivCVV Inference (2)" $
        testInference (\[(_, val1), (id2, _), (id3, _)] -> DivCVV val1 (newVar id2) (newVar id3)) [True, True, False] [False, False, True]
    describe "DivVCV Inference (1)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> DivVCV (newVar id1) val2 (newVar id3)) [False, False, False] [True, False, False]
    describe "DivVCV Inference (2)" $
        testInference (\[(id1, _), (_, val2), (id3, _)] -> DivVCV (newVar id1) val2 (newVar id3)) [True, True, False] [False, False, True]
    describe "DivVVV Inference (1, 2, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [False, False, False]
            [True, True, False]
    describe "DivVVV Inference (1, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "DivVVV Inference (2, 3, +)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [False, True, True]
    describe "DivVVV Inference (1, 2, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [False, False, False]
            [True, True, False]
    describe "DivVVV Inference (1, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "DivVVV Inference (2, 3, -)" $
        testInference (\[(id1, _), (id2, _), (id3, _)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [False, True, True]

type InputGenerator = IO (M.Map VariableId Rational, ThreeAddressCode Rational)

genInput :: ([(VariableId, Rational)] -> ThreeAddressCode Rational) -> [Bool] -> [Bool] -> Gen (M.Map VariableId Rational, ThreeAddressCode Rational)
genInput constructor allowZero startingAssignment = do
  -- Generating variable IDs
  let varIds = [1..length allowZero]
  -- Generating starting assignments
  startingAssignments <- mapM genValue allowZero
  -- Pairing variable IDs with the corresponding values
  let startingVarAssignments = zip varIds startingAssignments
  -- Selecting those which are in the starting assignment
  let filteredVarAssignments = map snd . filter fst $ zip startingAssignment startingVarAssignments
  -- Constructing ThreeAddressCode
  let tac = constructor startingVarAssignments
  -- Constructing the input for the test case
  return (M.fromList filteredVarAssignments, tac)
  where
    genValue allowZ = if allowZ then arbitrary else arbitrary `suchThat` (/= 0)

testInference :: ([(VariableId, Rational)] -> ThreeAddressCode Rational) -> [Bool] -> [Bool] -> SpecWith ()
testInference constructor allowZero startingAssignment = 
  it "correctly infers variable values" $ property $ do
    (startingVarAssignments, tac) <- genInput constructor allowZero startingAssignment
    let inferredAssignments = inferAssignment startingVarAssignments tac
    let finalAssignments = M.union inferredAssignments startingVarAssignments
    return $ case threeACEval finalAssignments tac of
      Nothing -> False -- The evaluation should not fail
      Just result -> not (M.null inferredAssignments) && result
