module ThreeAddress
    ( Variable(..), VariableId, newVar, ThreeAddressCode(..), SignedVar(..), Sig
    ) where

type VariableId = Int
data Variable = Variable (Maybe String) VariableId 
    deriving (Show, Eq, Ord)
newVar :: VariableId -> Variable
newVar = Variable Nothing

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