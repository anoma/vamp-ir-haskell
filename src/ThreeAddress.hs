module ThreeAddress
    ( Variable(..), VariableId, newVar, varId, ThreeAddressCode(..), SignedVar(..), Circuit, inferAssignment, threeACEval
    ) where

import qualified Data.Set as S
import qualified  Data.Map as M
import Control.Monad

type VariableId = Int
data Variable = Variable (Maybe String) VariableId 
    deriving (Show, Eq, Ord)
newVar :: VariableId -> Variable
newVar = Variable Nothing

varId :: Variable -> VariableId
varId (Variable _ vid) = vid

data SignedVar = Pos Variable | Neg Variable

data ThreeAddressCode f
    = EVC Variable f
    | EVV SignedVar Variable
    -- AddCCV f f Variable -- Variable can be removed in this case
    -- AddCVV f Variable Variable -- Can be turned into AddVCV
    | AddVCV Variable f Variable -- x = i + y
    | AddCVV f Variable Variable -- i = x + y
    | AddVVV SignedVar Variable Variable -- x = y + z
    -- MulCCV f f Variable -- Variable can be removed in this case
    | MulCVV f Variable Variable -- i = x * y
    | MulVCV Variable f Variable -- x = i * y
    | MulVVV SignedVar Variable Variable -- x = y * z
    -- Are the div constructors neccessary?
    | DivCCV f f Variable -- i = j / y
    -- DivCVC f Variable f -- Variable can be removed in this case
    | DivCVV f Variable Variable -- i = x / y
    | DivVCV Variable f Variable -- x = i / y
    -- DivVVC Variable Variable f -- Can be turned into MulVCV
    | DivVVV SignedVar Variable Variable -- x = y / z

threeACEval :: (Eq f, Fractional f) => M.Map VariableId f -> ThreeAddressCode f -> Maybe Bool
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
        return $ i == j / yVal
    DivCVV i x y -> do
        yVal <- M.lookup (varId y) assignments
        xVal <- M.lookup (varId x) assignments
        guard (yVal /= 0)
        return $ i == xVal / yVal
    DivVCV x i y -> do
        yVal <- M.lookup (varId y) assignments
        guard (yVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ xVal == i / yVal
    DivVVV (Pos x) y z -> do
        zVal <- M.lookup (varId z) assignments
        yVal <- M.lookup (varId y) assignments
        guard (zVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ xVal == yVal / zVal
    DivVVV (Neg x) y z -> do
        zVal <- M.lookup (varId z) assignments
        yVal <- M.lookup (varId y) assignments
        guard (zVal /= 0)
        xVal <- M.lookup (varId x) assignments
        return $ negate xVal == yVal / zVal

type Circuit f = [ThreeAddressCode f]

-- Extract variable ids from an instruction
variablesInTAC :: ThreeAddressCode f -> [VariableId]
variablesInTAC tac = case tac of
    EVC var _ -> [varId var]
    EVV signedVar var -> varId var
        : (case signedVar of
            Pos v -> [varId v]
            Neg v -> [varId v])
    AddVCV var _ var2 -> [varId var, varId var2]
    AddCVV _ var var2 -> [varId var, varId var2]
    AddVVV signedVar var var2 -> [varId var, varId var2] ++ (case signedVar of
        Pos v -> [varId v]
        Neg v -> [varId v])
    MulCVV _ var var2 -> [varId var, varId var2]
    MulVCV var _ var2 -> [varId var, varId var2]
    MulVVV signedVar var var2 -> [varId var, varId var2] ++ (case signedVar of
        Pos v -> [varId v]
        Neg v -> [varId v])
    DivCCV _ _ var -> [varId var]
    DivCVV _ var var2 -> [varId var, varId var2]
    DivVCV var _ var2 -> [varId var, varId var2]
    DivVVV signedVar var var2 -> [varId var, varId var2] ++ (case signedVar of
        Pos v -> [varId v]
        Neg v -> [varId v])

-- Build map from ids to indices of clauses referencing those ids
constructMap :: Circuit f -> M.Map VariableId (S.Set Int)
constructMap circuit = 
    foldl updateMap M.empty (zip [0..] circuit)
  where
    updateMap :: M.Map VariableId (S.Set Int) -> (Int, ThreeAddressCode f) -> M.Map VariableId (S.Set Int)
    updateMap acc (idx, tac) = 
        foldl (\m varId0 -> M.insertWith S.union varId0 (S.singleton idx) m) acc (variablesInTAC tac)

-- Try to infer an assignment from a 3ac clause
-- Note: This should only ever produce an assignment if that variable isn't already assigned
inferAssignment :: (Eq f, Fractional f) => M.Map VariableId f -> ThreeAddressCode f -> M.Map VariableId f
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
            (Just xVal, Nothing) -> M.singleton y (i - xVal)
            (Nothing, Just yVal) -> M.singleton x (i - yVal)
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
                | xVal /= 0 -> M.singleton y (i / xVal)
                | otherwise -> M.empty
            (Nothing, Just yVal)
                | i == 0 -> if yVal == 0 then M.empty else M.singleton x 0
                | yVal /= 0 -> M.singleton x (i / yVal)
                | otherwise -> M.empty
            _ -> M.empty

    MulVCV (Variable _ x) i (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing)
                | i /= 0 -> M.singleton y (xVal / i)
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
            (Just xVal, Just yVal, Nothing)
                | yVal == 0 ->  M.empty
                | otherwise ->
                    case signedVar of
                        Pos _ -> M.singleton z (xVal / yVal)
                        Neg _ -> M.singleton z (-xVal / yVal)
            (Just xVal, Nothing, Just zVal)
                | zVal == 0 -> M.empty
                | otherwise ->
                    case signedVar of
                        Pos _ -> M.singleton y (xVal / zVal)
                        Neg _ -> M.singleton y (-xVal / zVal)
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
                if i == 0 then M.empty  -- Cannot infer y
                else M.singleton y (j / i)

    DivCVV i (Variable _ x) (Variable _ y) ->
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) ->
                if i == 0 || xVal == 0 then M.empty -- Cannot infer y
                else M.singleton y (xVal / i)
            (Nothing, Just yVal) ->
                if yVal == 0 then M.empty -- Division by zero is undefined
                else M.singleton x (i * yVal)
            _ -> M.empty

    DivVCV (Variable _ x) i (Variable _ y) -> 
        let xValM = M.lookup x assignments
            yValM = M.lookup y assignments
        in case (xValM, yValM) of
            (Just xVal, Nothing) -> 
                if xVal == 0 || i == 0 then M.empty -- Cannot infer y
                else M.singleton y (i / xVal)
            (Nothing, Just yVal) -> 
                if yVal == 0 then M.empty -- Division by zero
                else M.singleton x (i / yVal)
            _ -> M.empty

    DivVVV signedVar (Variable _ y) (Variable _ z) -> 
        let x = case signedVar of
                    Pos (Variable _ i) -> i
                    Neg (Variable _ i) -> i
            xValM = M.lookup x assignments
            yValM = M.lookup y assignments
            zValM = M.lookup z assignments
        in case (xValM, yValM, zValM) of
            (Just xVal, Just yVal, Nothing)
                | xVal == 0 || yVal == 0 -> M.empty
                | otherwise ->
                    case signedVar of
                        Pos _ -> M.singleton z (yVal / xVal)
                        Neg _ -> M.singleton z (-yVal / xVal)
                        
            (Just xVal, Nothing, Just zVal)
                | zVal == 0 -> M.empty
                | otherwise ->
                    case signedVar of
                        Pos _ -> M.singleton y (xVal * zVal)
                        Neg _ -> M.singleton y (-xVal * zVal)
                        
            (Nothing, Just yVal, Just zVal)
                | zVal == 0 -> M.empty  -- division by zero
                | otherwise ->
                    case signedVar of
                        Pos _ -> M.singleton x (yVal / zVal)
                        Neg _ -> M.singleton x (- (yVal / zVal))
            _ -> M.empty

-- Given known assignments and a circuit, infer new assignments
inferAllAssignments :: (Eq f, Fractional f) => Circuit f -> M.Map VariableId f -> M.Map VariableId f
inferAllAssignments circuit assignments = go assignments (M.keysSet assignments)
  where
    circuitMap = constructMap circuit

    go oldAssignments newVars
      | S.null newVars = oldAssignments
      | otherwise =
          let clauseIndices = S.unions $ map (\v -> M.findWithDefault S.empty v circuitMap) (S.toList newVars)
              clauses = [circuit !! i | i <- S.toList clauseIndices]
              inferredAssignments = M.unions $ map (inferAssignment oldAssignments) clauses
          in go (M.union oldAssignments inferredAssignments) (M.keysSet inferredAssignments)