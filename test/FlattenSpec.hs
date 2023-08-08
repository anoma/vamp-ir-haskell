module FlattenSpec where

import Test.Hspec
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import qualified Data.List as L
import Control.Monad.State
import Test.QuickCheck
import ThreeAddress
import Constraints

testFlatten :: 
  ([Rational] -> Rational) -> 
  Maybe (Either Rational SignedVar) -> 
  [Bool] -> [Bool] ->
  (ArithExp Rational -> ArithExp Rational -> ArithExp Rational) -> Property
testFlatten cnstF lfix isVar isNegated e = forAll (vectorOf 2 (arbitrary `suchThat` (/= 0))) $ \values -> 
  let varMap = M.fromList $ zip [0, 1] values
      exp0 = case (head isVar, head isNegated) of
        (True, True) -> e (ANeg $ AVar (Variable Nothing 0))
        (True, False) -> e (AVar (Variable Nothing 0))
        (False, True) -> e (ANeg $ AConst $ head values)
        (False, False) -> e (AConst $ head values)
      exp1 = case (isVar!!1, isNegated!!1) of
        (True, True) -> exp0 (ANeg $ AVar (Variable Nothing 1))
        (True, False) -> exp0 (AVar (Variable Nothing 1))
        (False, True) -> exp0 (ANeg $ AConst $ values!!1)
        (False, False) -> exp0 (AConst $ values!!1)
      evalResult = evalArithExp varMap exp1
      initialState = ((S.empty, M.empty), 2)
      resultEither = case lfix of
        Just (Left _) -> runStateT (flatten (Just $ Left $ cnstF (zipWith (\n v -> if n then (-v) else v) isNegated values)) exp1) initialState
        _ -> runStateT (flatten lfix exp1) initialState
  in case resultEither of
      Left _ -> False
      Right ((value, codes), _) ->
        let finalMap = case lfix of
              Just (Right (Neg _)) -> case value of
                Right (Pos var) -> M.insert (varId var) (negate $ fromJust evalResult) varMap
                Right (Neg var) -> M.insert (varId var) (fromJust evalResult) varMap
                Left _ -> varMap
              _ -> case value of
                Right (Pos var) -> M.insert (varId var) (fromJust evalResult) varMap
                Right (Neg var) -> M.insert (varId var) (negate $ fromJust evalResult) varMap
                Left _ -> varMap
        in all (\code -> threeACEval finalMap code == Just True) codes

flattenSpec :: Spec
flattenSpec = describe "flatten function" $ do
  it "Addition (VV, ++, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, ++, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, ++, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, ++, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, True] [False, False] (AOp FAdd)
  it "Addition (VC, ++, No Set)" $ 
    property $ testFlatten sum Nothing [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, ++, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, ++, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, ++, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, False] [False, False] (AOp FAdd)
  it "Addition (CV, ++, No Set)" $ 
    property $ testFlatten sum Nothing [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, ++, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, ++, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, ++, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [False, True] [False, False] (AOp FAdd)
  it "Addition (CC, ++, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, False] (AOp FAdd)
  it "Addition (CC, ++, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FAdd)
  it "Addition (CC, ++, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FAdd)
  it "Addition (VV, -+, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [True, False] (AOp FAdd)
  it "Addition (VV, -+, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [True, False] (AOp FAdd)
  it "Addition (VV, -+, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [True, False] (AOp FAdd)
  it "Addition (VV, -+, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, True] [True, False] (AOp FAdd)
  it "Addition (VC, -+, No Set)" $ 
    property $ testFlatten sum Nothing [True, False] [True, False] (AOp FAdd)
  it "Addition (VC, -+, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [True, False] (AOp FAdd)
  it "Addition (VC, -+, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [True, False] (AOp FAdd)
  it "Addition (VC, -+, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, False] [True, False] (AOp FAdd)
  it "Addition (CV, -+, No Set)" $ 
    property $ testFlatten sum Nothing [False, True] [True, False] (AOp FAdd)
  it "Addition (CV, -+, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [True, False] (AOp FAdd)
  it "Addition (CV, -+, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [True, False] (AOp FAdd)
  it "Addition (CV, -+, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [False, True] [True, False] (AOp FAdd)
  it "Addition (CC, -+, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [True, False] (AOp FAdd)
  it "Addition (CC, -+, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [True, False] (AOp FAdd)
  it "Addition (CC, -+, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [True, False] (AOp FAdd)
  it "Addition (VV, +-, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, True] (AOp FAdd)
  it "Addition (VV, +-, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, True] (AOp FAdd)
  it "Addition (VV, +-, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, True] (AOp FAdd)
  it "Addition (VV, +-, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, True] [False, True] (AOp FAdd)
  it "Addition (VC, +-, No Set)" $ 
    property $ testFlatten sum Nothing [True, False] [False, True] (AOp FAdd)
  it "Addition (VC, +-, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, True] (AOp FAdd)
  it "Addition (VC, +-, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, True] (AOp FAdd)
  it "Addition (VC, +-, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, False] [False, True] (AOp FAdd)
  it "Addition (CV, +-, No Set)" $ 
    property $ testFlatten sum Nothing [False, True] [False, True] (AOp FAdd)
  it "Addition (CV, +-, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, True] (AOp FAdd)
  it "Addition (CV, +-, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, True] (AOp FAdd)
  it "Addition (CV, +-, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [False, True] [False, True] (AOp FAdd)
  it "Addition (CC, +-, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, True] (AOp FAdd)
  it "Addition (CC, +-, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, True] (AOp FAdd)
  it "Addition (CC, +-, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, True] (AOp FAdd)
  it "Addition (VV, --, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, --, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, --, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FAdd)
  it "Addition (VV, --, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, True] [False, False] (AOp FAdd)
  it "Addition (VC, --, No Set)" $ 
    property $ testFlatten sum Nothing [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, --, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, --, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FAdd)
  it "Addition (VC, --, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [True, False] [False, False] (AOp FAdd)
  it "Addition (CV, --, No Set)" $ 
    property $ testFlatten sum Nothing [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, --, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, --, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FAdd)
  it "Addition (CV, --, Set Const)" $ 
    property $ testFlatten sum (Just $ Left 0) [False, True] [False, False] (AOp FAdd)
  it "Addition (CC, --, No Set)" $ 
    property $ testFlatten sum Nothing [True, True] [False, False] (AOp FAdd)
  it "Addition (CC, --, Set Pos Var)" $ 
    property $ testFlatten sum (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FAdd)
  it "Addition (CC, --, Set Neg Var)" $ 
    property $ testFlatten sum (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FAdd)

  it "Subtraction (VV, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VC, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (CV, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CC, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (CC, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FSubtract)
  it "Subtraction (CC, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FSubtract)
  it "Subtraction (VV, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [True, False] (AOp FSubtract)
  it "Subtraction (VV, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [True, False] (AOp FSubtract)
  it "Subtraction (VV, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [True, False] (AOp FSubtract)
  it "Subtraction (VV, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, True] [True, False] (AOp FSubtract)
  it "Subtraction (VC, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, False] [True, False] (AOp FSubtract)
  it "Subtraction (VC, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [True, False] (AOp FSubtract)
  it "Subtraction (VC, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [True, False] (AOp FSubtract)
  it "Subtraction (VC, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, False] [True, False] (AOp FSubtract)
  it "Subtraction (CV, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [False, True] [True, False] (AOp FSubtract)
  it "Subtraction (CV, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [True, False] (AOp FSubtract)
  it "Subtraction (CV, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [True, False] (AOp FSubtract)
  it "Subtraction (CV, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [False, True] [True, False] (AOp FSubtract)
  it "Subtraction (CC, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [True, False] (AOp FSubtract)
  it "Subtraction (CC, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [True, False] (AOp FSubtract)
  it "Subtraction (CC, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [True, False] (AOp FSubtract)
  it "Subtraction (VV, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, True] (AOp FSubtract)
  it "Subtraction (VV, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, True] (AOp FSubtract)
  it "Subtraction (VV, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, True] (AOp FSubtract)
  it "Subtraction (VV, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, True] [False, True] (AOp FSubtract)
  it "Subtraction (VC, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, False] [False, True] (AOp FSubtract)
  it "Subtraction (VC, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, True] (AOp FSubtract)
  it "Subtraction (VC, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, True] (AOp FSubtract)
  it "Subtraction (VC, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, False] [False, True] (AOp FSubtract)
  it "Subtraction (CV, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [False, True] [False, True] (AOp FSubtract)
  it "Subtraction (CV, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, True] (AOp FSubtract)
  it "Subtraction (CV, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, True] (AOp FSubtract)
  it "Subtraction (CV, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [False, True] [False, True] (AOp FSubtract)
  it "Subtraction (CC, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, True] (AOp FSubtract)
  it "Subtraction (CC, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, True] (AOp FSubtract)
  it "Subtraction (CC, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, True] (AOp FSubtract)
  it "Subtraction (VV, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VV, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (VC, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (VC, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [True, False] [False, False] (AOp FSubtract)
  it "Subtraction (CV, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CV, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Left 0) [False, True] [False, False] (AOp FSubtract)
  it "Subtraction (CC, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x-y) Nothing [True, True] [False, False] (AOp FSubtract)
  it "Subtraction (CC, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FSubtract)
  it "Subtraction (CC, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x-y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FSubtract)

  it "Multiplication (VV, ++, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, ++, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, ++, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, ++, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VC, ++, No Set)" $ 
    property $ testFlatten product Nothing [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, ++, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, ++, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, ++, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (CV, ++, No Set)" $ 
    property $ testFlatten product Nothing [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, ++, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, ++, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, ++, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CC, ++, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (CC, ++, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FMultiply)
  it "Multiplication (CC, ++, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FMultiply)
  it "Multiplication (VV, -+, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [True, False] (AOp FMultiply)
  it "Multiplication (VV, -+, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [True, False] (AOp FMultiply)
  it "Multiplication (VV, -+, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [True, False] (AOp FMultiply)
  it "Multiplication (VV, -+, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, True] [True, False] (AOp FMultiply)
  it "Multiplication (VC, -+, No Set)" $ 
    property $ testFlatten product Nothing [True, False] [True, False] (AOp FMultiply)
  it "Multiplication (VC, -+, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [True, False] (AOp FMultiply)
  it "Multiplication (VC, -+, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [True, False] (AOp FMultiply)
  it "Multiplication (VC, -+, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, False] [True, False] (AOp FMultiply)
  it "Multiplication (CV, -+, No Set)" $ 
    property $ testFlatten product Nothing [False, True] [True, False] (AOp FMultiply)
  it "Multiplication (CV, -+, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [True, False] (AOp FMultiply)
  it "Multiplication (CV, -+, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [True, False] (AOp FMultiply)
  it "Multiplication (CV, -+, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [False, True] [True, False] (AOp FMultiply)
  it "Multiplication (CC, -+, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [True, False] (AOp FMultiply)
  it "Multiplication (CC, -+, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [True, False] (AOp FMultiply)
  it "Multiplication (CC, -+, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [True, False] (AOp FMultiply)
  it "Multiplication (VV, +-, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, True] (AOp FMultiply)
  it "Multiplication (VV, +-, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, True] (AOp FMultiply)
  it "Multiplication (VV, +-, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, True] (AOp FMultiply)
  it "Multiplication (VV, +-, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, True] [False, True] (AOp FMultiply)
  it "Multiplication (VC, +-, No Set)" $ 
    property $ testFlatten product Nothing [True, False] [False, True] (AOp FMultiply)
  it "Multiplication (VC, +-, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, True] (AOp FMultiply)
  it "Multiplication (VC, +-, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, True] (AOp FMultiply)
  it "Multiplication (VC, +-, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, False] [False, True] (AOp FMultiply)
  it "Multiplication (CV, +-, No Set)" $ 
    property $ testFlatten product Nothing [False, True] [False, True] (AOp FMultiply)
  it "Multiplication (CV, +-, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, True] (AOp FMultiply)
  it "Multiplication (CV, +-, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, True] (AOp FMultiply)
  it "Multiplication (CV, +-, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [False, True] [False, True] (AOp FMultiply)
  it "Multiplication (CC, +-, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, True] (AOp FMultiply)
  it "Multiplication (CC, +-, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, True] (AOp FMultiply)
  it "Multiplication (CC, +-, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, True] (AOp FMultiply)
  it "Multiplication (VV, --, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, --, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, --, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VV, --, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (VC, --, No Set)" $ 
    property $ testFlatten product Nothing [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, --, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, --, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (VC, --, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [True, False] [False, False] (AOp FMultiply)
  it "Multiplication (CV, --, No Set)" $ 
    property $ testFlatten product Nothing [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, --, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, --, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CV, --, Set Const)" $ 
    property $ testFlatten product (Just $ Left 0) [False, True] [False, False] (AOp FMultiply)
  it "Multiplication (CC, --, No Set)" $ 
    property $ testFlatten product Nothing [True, True] [False, False] (AOp FMultiply)
  it "Multiplication (CC, --, Set Pos Var)" $ 
    property $ testFlatten product (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FMultiply)
  it "Multiplication (CC, --, Set Neg Var)" $ 
    property $ testFlatten product (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FMultiply)

  it "Division (VV, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, False] (AOp FDivide)
  it "Division (VV, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FDivide)
  it "Division (VV, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FDivide)
  it "Division (VV, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, True] [False, False] (AOp FDivide)
  it "Division (VC, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, False] [False, False] (AOp FDivide)
  it "Division (VC, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FDivide)
  it "Division (VC, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FDivide)
  it "Division (VC, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, False] [False, False] (AOp FDivide)
  it "Division (CV, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [False, True] [False, False] (AOp FDivide)
  it "Division (CV, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FDivide)
  it "Division (CV, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FDivide)
  it "Division (CV, ++, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [False, True] [False, False] (AOp FDivide)
  it "Division (CC, ++, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, False] (AOp FDivide)
  it "Division (CC, ++, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FDivide)
  it "Division (CC, ++, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FDivide)
  it "Division (VV, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [True, False] (AOp FDivide)
  it "Division (VV, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [True, False] (AOp FDivide)
  it "Division (VV, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [True, False] (AOp FDivide)
  it "Division (VV, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, True] [True, False] (AOp FDivide)
  it "Division (VC, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, False] [True, False] (AOp FDivide)
  it "Division (VC, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [True, False] (AOp FDivide)
  it "Division (VC, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [True, False] (AOp FDivide)
  it "Division (VC, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, False] [True, False] (AOp FDivide)
  it "Division (CV, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [False, True] [True, False] (AOp FDivide)
  it "Division (CV, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [True, False] (AOp FDivide)
  it "Division (CV, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [True, False] (AOp FDivide)
  it "Division (CV, -+, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [False, True] [True, False] (AOp FDivide)
  it "Division (CC, -+, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [True, False] (AOp FDivide)
  it "Division (CC, -+, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [True, False] (AOp FDivide)
  it "Division (CC, -+, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [True, False] (AOp FDivide)
  it "Division (VV, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, True] (AOp FDivide)
  it "Division (VV, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, True] (AOp FDivide)
  it "Division (VV, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, True] (AOp FDivide)
  it "Division (VV, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, True] [False, True] (AOp FDivide)
  it "Division (VC, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, False] [False, True] (AOp FDivide)
  it "Division (VC, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, True] (AOp FDivide)
  it "Division (VC, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, True] (AOp FDivide)
  it "Division (VC, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, False] [False, True] (AOp FDivide)
  it "Division (CV, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [False, True] [False, True] (AOp FDivide)
  it "Division (CV, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, True] (AOp FDivide)
  it "Division (CV, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, True] (AOp FDivide)
  it "Division (CV, +-, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [False, True] [False, True] (AOp FDivide)
  it "Division (CC, +-, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, True] (AOp FDivide)
  it "Division (CC, +-, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, True] (AOp FDivide)
  it "Division (CC, +-, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, True] (AOp FDivide)
  it "Division (VV, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, False] (AOp FDivide)
  it "Division (VV, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, True] [False, False] (AOp FDivide)
  it "Division (VV, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, True] [False, False] (AOp FDivide)
  it "Division (VV, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, True] [False, False] (AOp FDivide)
  it "Division (VC, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, False] [False, False] (AOp FDivide)
  it "Division (VC, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [True, False] [False, False] (AOp FDivide)
  it "Division (VC, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [True, False] [False, False] (AOp FDivide)
  it "Division (VC, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [True, False] [False, False] (AOp FDivide)
  it "Division (CV, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [False, True] [False, False] (AOp FDivide)
  it "Division (CV, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, True] [False, False] (AOp FDivide)
  it "Division (CV, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, True] [False, False] (AOp FDivide)
  it "Division (CV, --, Set Const)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Left 0) [False, True] [False, False] (AOp FDivide)
  it "Division (CC, --, No Set)" $ 
    property $ testFlatten (\[x, y] -> x/y) Nothing [True, True] [False, False] (AOp FDivide)
  it "Division (CC, --, Set Pos Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Pos $ Variable Nothing 2) [False, False] [False, False] (AOp FDivide)
  it "Division (CC, --, Set Neg Var)" $ 
    property $ testFlatten (\[x, y] -> x/y) (Just $ Right $ Neg $ Variable Nothing 2) [False, False] [False, False] (AOp FDivide)

  -- Add more test cases here

