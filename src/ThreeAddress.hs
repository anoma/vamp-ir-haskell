module ThreeAddress
    ( Variable(..), VariableId, newVar, ThreeAddressCode(..), SignedVar(..), Sig, Circuit
    ) where

import qualified Data.Set as S
import qualified  Data.Map as M

type VariableId = Int
data Variable = Variable (Maybe String) VariableId 
    deriving (Show, Eq, Ord)
newVar :: VariableId -> Variable
newVar = Variable Nothing

getVarId :: Variable -> VariableId
getVarId (Variable _ vid) = vid

data Sig = Sig Int Int

-- data Free = FVar Variable | FFresh Sig

data SignedVar = Pos Variable | Neg Variable

data ThreeAddressCode
    = EVC Variable Integer
    | EVV SignedVar Variable
    -- AddCCV Integer Integer Variable -- Variable can be removed in this case
    -- AddCVV Integer Variable Variable -- Can be turned into AddVCV
    | AddVCV Variable Integer Variable -- x = i + y
    | AddCVV Integer Variable Variable -- i = x + y
    | AddVVV SignedVar Variable Variable -- x = y + z
    -- MulCCV Integer Integer Variable -- Variable can be removed in this case
    | MulCVV Integer Variable Variable -- i = x * y
    | MulVCV Variable Integer Variable -- x = i * y
    | MulVVV SignedVar Variable Variable -- x = y * z
    -- Are the div constructors neccessary?
    | DivCCV Integer Integer Variable -- i = j / y
    -- DivCVC Integer Variable Integer -- Variable can be removed in this case
    | DivCVV Integer Variable Variable -- i = x / y
    | DivVCV Variable Integer Variable -- x = i / y
    -- DivVVC Variable Variable Integer -- Can be turned into MulVCV
    | DivVVV SignedVar Variable Variable -- x = y / z

type Circuit = [ThreeAddressCode]

-- Extract variable ids from an instruction
variablesInTAC :: ThreeAddressCode -> [VariableId]
variablesInTAC tac = case tac of
    EVC var _ -> [getVarId var]
    EVV signedVar var -> getVarId var
        : (case signedVar of
            Pos v -> [getVarId v]
            Neg v -> [getVarId v])
    AddVCV var _ var2 -> [getVarId var, getVarId var2]
    AddCVV _ var var2 -> [getVarId var, getVarId var2]
    AddVVV signedVar var var2 -> [getVarId var, getVarId var2] ++ (case signedVar of
        Pos v -> [getVarId v]
        Neg v -> [getVarId v])
    MulCVV _ var var2 -> [getVarId var, getVarId var2]
    MulVCV var _ var2 -> [getVarId var, getVarId var2]
    MulVVV signedVar var var2 -> [getVarId var, getVarId var2] ++ (case signedVar of
        Pos v -> [getVarId v]
        Neg v -> [getVarId v])
    DivCCV _ _ var -> [getVarId var]
    DivCVV _ var var2 -> [getVarId var, getVarId var2]
    DivVCV var _ var2 -> [getVarId var, getVarId var2]
    DivVVV signedVar var var2 -> [getVarId var, getVarId var2] ++ (case signedVar of
        Pos v -> [getVarId v]
        Neg v -> [getVarId v])

-- Build map from ids to indices of clauses referencing those ids
constructMap :: Circuit -> M.Map VariableId (S.Set Int)
constructMap circuit = 
    foldl updateMap M.empty (zip [0..] circuit)
  where
    updateMap :: M.Map VariableId (S.Set Int) -> (Int, ThreeAddressCode) -> M.Map VariableId (S.Set Int)
    updateMap acc (idx, tac) = 
        foldl (\m varId -> M.insertWith S.union varId (S.singleton idx) m) acc (variablesInTAC tac)

-- Try to infer an assignment from an instruction
inferAssignment :: M.Map VariableId Integer -> ThreeAddressCode -> M.Map VariableId Integer
inferAssignment assignments tac = case tac of
    EVC (Variable _ x) value ->
        let xValM = M.lookup x assignments
        in case xValM of
            (Just _) -> M.empty
            Nothing -> M.singleton x value
    
    EVV signedVar (Variable _ y) -> 
        let x = case signedVar of
                    Pos (Variable _ i) -> i
                    Neg (Variable _ i) -> i
            xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) -> 
                case signedVar of
                    Pos _ -> M.singleton y xVal
                    Neg _ -> M.singleton y (-xVal)
            (Nothing, Just yVal) -> case signedVar of
                    Pos _ -> M.singleton x yVal
                    Neg _ -> M.singleton x (-yVal)
            _ -> M.empty
            
    AddVCV (Variable _ x) i (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Nothing, Just yVal) -> M.singleton x (i + yVal)
            (Just xVal, Nothing) -> M.singleton y (xVal - i)
            _ -> M.empty

    AddCVV i (Variable _ x) (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) -> M.singleton y (i + xVal)
            (Nothing, Just yVal) -> M.singleton x (yVal - i)
            _ -> M.empty

    AddVVV signedVar (Variable _ y) (Variable _ z) -> 
        let x = case signedVar of
                    Pos (Variable _ i) -> i
                    Neg (Variable _ i) -> i
            xValM = M.lookup x assignments
            yValM = M.lookup y assignments
            zValM = M.lookup z assignments
        in case (xValM, yValM, zValM) of
            (Just xVal, Just yVal, Nothing) -> 
                case signedVar of
                    Pos _ -> M.singleton z (xVal - yVal)
                    Neg _ -> M.singleton z (-xVal - yVal)
            (Just xVal, Nothing, Just zVal) ->
                case signedVar of
                    Pos _ -> M.singleton y (xVal - zVal)
                    Neg _ -> M.singleton y (-xVal - zVal)
            (Nothing, Just yVal, Just zVal) ->
                case signedVar of
                    Pos _ -> M.singleton x (yVal + zVal)
                    Neg _ -> M.singleton x (-(yVal + zVal))
            _ -> M.empty

    MulCVV i (Variable _ x) (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) 
                | i == 0 -> if xVal == 0 then M.empty else M.singleton y 0
                | xVal /= 0 -> M.singleton y (i `div` xVal)
                | otherwise -> M.empty
            (Nothing, Just yVal)
                | i == 0 -> if yVal == 0 then M.empty else M.singleton x 0
                | yVal /= 0 -> M.singleton x (i `div` yVal)
                | otherwise -> M.empty
            _ -> M.empty

    MulVCV (Variable _ x) i (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing)
                | xVal == 0 && i /= 0 -> M.singleton y 0
                | xVal /= 0 && i /= 0 -> M.singleton y (xVal `div` i)
                | otherwise -> M.empty
            (Nothing, Just yVal) -> M.singleton x (i * yVal)
            (Nothing, Nothing) 
                | i == 0 -> M.singleton x 0
                | otherwise -> M.empty
            _ -> M.empty

    MulVVV signedVar (Variable _ y) (Variable _ z) -> 
        let x = case signedVar of
                    Pos (Variable _ i) -> i
                    Neg (Variable _ i) -> i
            xValM = M.lookup x assignments
            yValM = M.lookup y assignments
            zValM = M.lookup z assignments
        in case (xValM, yValM, zValM) of
            (Just xVal, Just yVal, Nothing) -> 
                if yVal == 0 then M.empty
                else
                    case signedVar of
                        Pos _ -> M.singleton z (xVal `div` yVal)
                        Neg _ -> M.singleton z (-xVal `div` yVal)
            (Just xVal, Nothing, Just zVal) -> 
                if zVal == 0 then M.empty
                else
                    case signedVar of
                        Pos _ -> M.singleton y (xVal `div` zVal)
                        Neg _ -> M.singleton y (-xVal `div` zVal)
            (Nothing, Just yVal, Just zVal) -> 
                case signedVar of
                    Pos _ -> M.singleton x (yVal * zVal)
                    Neg _ -> M.singleton x (-(yVal * zVal))
            (Nothing, Just 0, Nothing) -> M.singleton x 0
            (Nothing, Nothing, Just 0) -> M.singleton x 0
            _ -> M.empty

    DivCCV i j (Variable _ y) -> 
        let yValM = M.lookup y assignments
        in case yValM of
            Just _ -> M.empty
            Nothing -> 
                if i == 0 then M.empty  -- Cannot infer y when i is zero
                else M.singleton y (j `div` i)  -- Inferring y = j / i

    DivCVV i (Variable _ x) (Variable _ y) ->
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) ->
                if i == 0 || xVal == 0 then M.empty -- Cannot infer y
                else M.singleton y (xVal `div` i)
            (Nothing, Just yVal) ->
                if yVal == 0 then M.empty -- Division by zero is undefined
                else M.singleton x (i * yVal)
            _ -> M.empty -- Any other case, no new inference

    DivVCV (Variable _ x) i (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) -> 
                if xVal == 0 || i == 0 then M.empty  -- Cannot infer y
                else M.singleton y (i `div` xVal)
            (Nothing, Just yVal) -> 
                if yVal == 0 then M.empty  -- Division by zero is undefined
                else M.singleton x (i `div` yVal)
            _ -> M.empty -- Any other case, no new inference

    DivVVV signedVar (Variable _ y) (Variable _ z) -> 
        let x = case signedVar of
                    Pos (Variable _ i) -> i
                    Neg (Variable _ i) -> i
            xValM = M.lookup x assignments
            yValM = M.lookup y assignments
            zValM = M.lookup z assignments
        in case (xValM, yValM, zValM) of
            (Just _, Just _, Just _) -> M.empty
            (Just xVal, Just yVal, Nothing) -> 
                -- x and y known; infer z
                if xVal == 0 || yVal == 0 then M.empty
                else 
                    case signedVar of
                        Pos _ -> M.singleton z (yVal `div` xVal)
                        Neg _ -> M.singleton z (-yVal `div` xVal)
                        
            (Just xVal, Nothing, Just zVal) -> 
                -- x and z known; infer y
                if zVal == 0 then M.empty
                else 
                    case signedVar of
                        Pos _ -> M.singleton y (xVal * zVal)
                        Neg _ -> M.singleton y (-xVal * zVal)
                        
            (Nothing, Just yVal, Just zVal) -> 
                -- y and z known; infer x
                if zVal == 0 then M.empty  -- division by zero
                else
                    case signedVar of
                        Pos _ -> M.singleton x (yVal `div` zVal)
                        Neg _ -> M.singleton x (- (yVal `div` zVal))
            _ -> M.empty

-- Given known assignments and a circuit, infer new assignments
inferAllAssignments :: Circuit -> M.Map VariableId Integer -> M.Map VariableId Integer
inferAllAssignments circuit assignments = go assignments assignments
  where
    circuitMap = constructMap circuit

    go :: M.Map VariableId Integer -> M.Map VariableId Integer -> M.Map VariableId Integer
    go oldAssignments newAssignments
      | M.null newAssignments = oldAssignments
      | otherwise =
          let newVars = M.keysSet newAssignments
              clauseIndices = S.unions $ map (\v -> M.findWithDefault S.empty v circuitMap) (S.toList newVars)
              clauses = [circuit !! i | i <- S.toList clauseIndices]
              inferredAssignments = M.unions $ map (inferAssignment oldAssignments) clauses
          in go (M.union oldAssignments inferredAssignments) inferredAssignments