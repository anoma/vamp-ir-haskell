module ThreeACSpec where

import Test.Hspec
import qualified Data.Map as M
import Test.QuickCheck
import ThreeAddress
import Control.Monad

threeACEval :: M.Map VariableId Integer -> ThreeAddressCode -> Maybe Bool
threeACEval assignments tac = case tac of
    EVC x i -> (== i) <$> M.lookup (varId x) assignments
    EVV (Pos x) z -> (==) <$> M.lookup (varId x) assignments <*> M.lookup (varId z) assignments
    EVV (Neg x) z -> (==) <$> (negate <$> M.lookup (varId x) assignments) <*> M.lookup (varId z) assignments
    AddVCV x i y -> (==) <$> M.lookup (varId x) assignments <*> ((i +) <$> M.lookup (varId y) assignments)
    AddCVV i x y -> (== i) <$> ((+) <$> M.lookup (varId x) assignments <*> M.lookup (varId y) assignments)
    AddVVV (Pos x) y z -> (==) <$> M.lookup (varId x) assignments <*> ((+) <$> M.lookup (varId y) assignments <*> M.lookup (varId z) assignments)
    AddVVV (Neg x) y z -> (==) <$> (negate <$> M.lookup (varId x) assignments) <*> ((+) <$> M.lookup (varId y) assignments <*> M.lookup (varId z) assignments)
    MulCVV i x y -> (== i) <$> ((*) <$> M.lookup (varId x) assignments <*> M.lookup (varId y) assignments)
    MulVCV x i y -> (==) <$> M.lookup (varId x) assignments <*> ((i *) <$> M.lookup (varId y) assignments)
    MulVVV (Pos x) y z -> (==) <$> M.lookup (varId x) assignments <*> ((*) <$> M.lookup (varId y) assignments <*> M.lookup (varId z) assignments)
    MulVVV (Neg x) y z -> (==) <$> (negate <$> M.lookup (varId x) assignments) <*> ((*) <$> M.lookup (varId y) assignments <*> M.lookup (varId z) assignments)
    DivCCV i j y -> do
        yVal <- M.lookup (varId y) assignments
        guard (yVal /= 0)
        return $ i == j `div` yVal
    DivCVV i x y -> do
        yVal <- M.lookup (varId y) assignments
        xVal <- M.lookup (varId x) assignments
        guard (yVal /= 0)
        return $ i == xVal `div` yVal
    DivVCV x i y -> do
        yVal <- M.lookup (varId y) assignments
        guard (yVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ xVal == i `div` yVal
    DivVVV (Pos x) y z -> do
        zVal <- M.lookup (varId z) assignments
        yVal <- M.lookup (varId y) assignments
        guard (zVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ xVal == yVal `div` zVal
    DivVVV (Neg x) y z -> do
        zVal <- M.lookup (varId z) assignments
        yVal <- M.lookup (varId y) assignments
        guard (zVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ negate xVal == yVal `div` zVal

-- Note: A lot of these currently fail because we aren't using an actual field for division.
inferAssignmentSpec :: Spec
inferAssignmentSpec = describe "inferAssignment" $ do
    describe "EVC Inference" $ 
        testInference (\[(id1, val1), (id2, val2)] -> EVC (newVar id1) val2) [True, True] [False, False]
    describe "EVV Inference (1, with positive x)" $ 
        testInference (\[(id1, val1), (id2, val2)] -> EVV (Pos (newVar id1)) (newVar id2)) [True, True] [True, False]
    describe "EVV Inference (2, with positive x)" $ 
        testInference (\[(id1, val1), (id2, val2)] -> EVV (Pos (newVar id1)) (newVar id2)) [True, True] [False, True]
    describe "EVV Inference (1, with negative x)" $ 
        testInference (\[(id1, val1), (id2, val2)] -> EVV (Neg (newVar id1)) (newVar id2)) [True, True] [True, False]
    describe "EVV Inference (righy, with negative x)" $ 
        testInference (\[(id1, val1), (id2, val2)] -> EVV (Neg (newVar id1)) (newVar id2)) [True, True] [False, True]
    describe "AddVCV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVCV (newVar id1) val2 (newVar id3)) [True, True, True] [True, False, False]
    describe "AddVCV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVCV (newVar id1) val2 (newVar id3)) [True, True, True] [False, False, True]
    describe "AddCVV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddCVV val1 (newVar id2) (newVar id3)) [True, True, True] [False, True, False]
    describe "AddCVV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddCVV val1 (newVar id2) (newVar id3)) [True, True, True] [False, False, True]
    describe "AddVVV Inference (1, 2, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, True, False]
    describe "AddVVV Inference (1, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, False, True]
    describe "AddVVV Inference (2, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "AddVVV Inference (1, 2, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, True, False]
    describe "AddVVV Inference (1, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [True, False, True]
    describe "AddVVV Inference (2, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> AddVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "MulCVV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulCVV val1 (newVar id2) (newVar id3)) [True, False, True] [False, True, False]
    describe "MulCVV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulCVV val1 (newVar id2) (newVar id3)) [True, True, False] [False, False, True]
    describe "MulVCV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVCV (newVar id1) val2 (newVar id3)) [True, False, True] [True, False, False]
    describe "MulVCV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVCV (newVar id1) val2 (newVar id3)) [True, True, True] [False, False, True]
    describe "MulVVV Inference (1, 2, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, False, True]
            [True, True, False]
    describe "MulVVV Inference (1, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "MulVVV Inference (2, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "MulVVV Inference (1, 2, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, False, True]
            [True, True, False]
    describe "MulVVV Inference (1, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "MulVVV Inference (2, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> MulVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, True]
            [False, True, True]
    describe "DivCCV Inference" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivCCV val1 val2 (newVar id3)) [True, True, False] [False, False, False]
    describe "DivCVV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivCVV val1 (newVar id2) (newVar id3)) [True, True, False] [False, True, False]
    describe "DivCVV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivCVV val1 (newVar id2) (newVar id3)) [True, True, False] [False, False, True]
    describe "DivVCV Inference (1)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVCV (newVar id1) val2 (newVar id3)) [True, True, False] [True, False, False]
    describe "DivVCV Inference (2)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVCV (newVar id1) val2 (newVar id3)) [True, True, False] [False, False, True]
    describe "DivVVV Inference (1, 2, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, True, False]
    describe "DivVVV Inference (1, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "DivVVV Inference (2, 3, +)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Pos (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [False, True, True]
    describe "DivVVV Inference (1, 2, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, True, False]
    describe "DivVVV Inference (1, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [True, False, True]
    describe "DivVVV Inference (2, 3, -)" $
        testInference (\[(id1, val1), (id2, val2), (id3, val3)] -> DivVVV (Neg (newVar id1)) (newVar id2) (newVar id3)) [True, True, False]
            [False, True, True]

type InputGenerator = IO (M.Map VariableId Integer, ThreeAddressCode)

genInput :: ([(VariableId, Integer)] -> ThreeAddressCode) -> [Bool] -> [Bool] -> Gen (M.Map VariableId Integer, ThreeAddressCode)
genInput constructor allowZero startingAssignment = do
  -- Generating variable IDs
  let varIds = [1..length allowZero]
  -- Generating starting assignments
  startingAssignments <- mapM genValue (zip startingAssignment allowZero)
  -- Pairing variable IDs with the corresponding values
  let startingVarAssignments = zip varIds startingAssignments
  -- Selecting those which are in the starting assignment
  let filteredVarAssignments = map snd . filter fst $ zip startingAssignment startingVarAssignments
  -- Constructing ThreeAddressCode
  let tac = constructor startingVarAssignments
  -- Constructing the input for the test case
  return (M.fromList filteredVarAssignments, tac)
  where
    genValue (startAssign, allowZ) = if not startAssign then return 0 else genValue' allowZ
    genValue' allowZ = if allowZ then arbitrary else arbitrary `suchThat` (/= 0)

testInference :: ([(VariableId, Integer)] -> ThreeAddressCode) -> [Bool] -> [Bool] -> SpecWith ()
testInference constructor allowZero startingAssignment = 
  it "correctly infers variable values" $ property $ do
    (startingVarAssignments, tac) <- genInput constructor allowZero startingAssignment
    let inferredAssignments = inferAssignment startingVarAssignments tac
    let finalAssignments = M.union inferredAssignments startingVarAssignments
    return $ case threeACEval finalAssignments tac of
      Nothing -> False -- The evaluation should not fail
      Just result -> not (M.null inferredAssignments) && result
