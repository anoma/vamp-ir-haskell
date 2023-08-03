module Constraints
    ( ArithExp(..), Clause(..), Constraints,
      Variable(..), VariableId, Sig, varid, FieldOp(..), 
    ) where

import Control.Monad.State
import ThreeAddress
import Data.Bifunctor
import qualified Data.Set as S
import qualified  Data.Map as M

varid :: Variable -> VariableId
varid (Variable _ i) = i

data FieldOp
    = FDivide
    | FMultiply
    | FAdd
    | FSubtract
    deriving (Show, Eq)

data ArithExp
    = AVar Variable
    | AFresh Sig
    | AConst Integer
    | ANeg ArithExp
    | AOp FieldOp ArithExp ArithExp

data Clause = ClEq ArithExp ArithExp

type Constraints = [Clause]

type FlatM x = StateT ((S.Set Variable, M.Map VariableId Sig), VariableId) (Either String) x

-- Produces a list of three address codes equivalent to the expression
-- along with the variable that can be used as the head of the expression
-- state acumulates free variables, fresh dependencies, and used names
-- First arg is a possible variable that can be used to prevent new variables; handles clause equations
flatten :: Maybe (Either Integer SignedVar) -> ArithExp -> FlatM (Either Integer SignedVar, [ThreeAddressCode])
flatten hyv (AVar var) = do
    modify $ first $ first (S.insert var)
    let def x = return (Right $ Pos var, x)
    case hyv of
        Nothing -> def []
        Just (Left i) -> def [EVC var i]
        Just (Right x) -> def [EVV x var]
flatten hyv (AFresh sig) = do
    (_, newid) <- get
    let newvar = newVar newid
    modify $ \((free, fresh), ids) -> ((free, M.insert newid sig fresh), ids + 1)
    let def x = return (Right $ Pos $ newvar, x)
    case hyv of
        Nothing -> def []
        Just (Left i) -> def [EVC newvar i]
        Just (Right x) -> def [EVV x newvar]
flatten hyv (AConst i) = do
    let def x = return (Left i, x)
    case hyv of
        Nothing -> def []
        Just (Left j) -> 
            if i /= j
            then lift $ Left "Different constants compared during 3ac generation"
            else def []
        Just (Right (Pos x)) -> def [EVC x i]
        Just (Right (Neg x)) -> def [EVC x (-i)]
flatten hyv (ANeg e) = do
    (hd, body) <- flatten Nothing e
    let def x y = return (x, y ++ body)
    case hd of
        (Left i) -> case hyv of
            Nothing -> def (Left (-i)) []
            Just (Left j) -> 
                if i /= (-j)
                then lift $ Left "Different constants compared during 3ac generation"
                else def (Left (-i)) []
            Just (Right (Pos x)) -> def (Left (-i)) [EVC x (-i)]
            Just (Right (Neg x)) -> def (Left (-i)) [EVC x i]
        (Right (Pos x)) -> def (Right $ Neg x) $ case hyv of
            Nothing -> []
            Just (Left j) -> [EVC x j]
            Just (Right y) -> [EVV y x]
        (Right (Neg x)) -> def (Right $ Pos x) $ case hyv of
            Nothing -> []
            Just (Left j) -> [EVC x (-j)]
            Just (Right (Pos y)) -> [EVV (Neg x) y]
            Just (Right (Neg y)) -> [EVV (Pos x) y]
flatten Nothing (AOp op e1 e2) = do
    (head1, body1) <- flatten Nothing e1
    (head2, body2) <- flatten Nothing e2
    (_, newid) <- get
    let newvar = newVar newid
    -- Default return; should be used unless return is a constant
    let def a = do
            modify $ second (+1)
            return (Right $ Pos newvar, a:body1 ++ body2)
    case (op, head1, head2) of
        -- Addition
        (FAdd, Left i1, Left i2) -> return (Left $ i1 + i2, body1 ++ body2)
        (FAdd, Right (Pos x), Left i) -> def $ AddVCV newvar i x
        (FAdd, Left i, Right (Pos x)) -> def $ AddVCV newvar i x
        (FAdd, Right (Neg x), Left i) -> def $ AddVCV newvar (-i) x
        (FAdd, Left i, Right (Neg x)) -> def $ AddVCV newvar (-i) x
        (FAdd, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Pos newvar) x y
        (FAdd, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Pos y) newvar x
        (FAdd, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Pos x) newvar y
        (FAdd, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Neg newvar) x y
        -- Subtraction
        (FSubtract, Left i1, Left i2) -> return (Left $ i1 - i2, body1 ++ body2)
        (FSubtract, Right (Pos x), Left i) -> def $ AddVCV newvar (-i) x
        (FSubtract, Left i, Right (Pos x)) -> def $ AddCVV i newvar x
        (FSubtract, Right (Neg x), Left i) -> def $ AddCVV (-i) newvar x
        (FSubtract, Left i, Right (Neg x)) -> def $ AddVCV newvar i x
        (FSubtract, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Pos x) newvar y
        (FSubtract, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Neg newvar) x y
        (FSubtract, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Pos newvar) x y
        (FSubtract, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Pos y) newvar x
        -- Multiplication
        (FMultiply, Left i1, Left i2) -> return (Left $ i1 * i2, body1 ++ body2)
        (FMultiply, Right (Pos x), Left i) -> def $ MulVCV newvar i x
        (FMultiply, Left i, Right (Pos x)) -> def $ MulVCV newvar i x
        (FMultiply, Right (Neg x), Left i) -> def $ MulVCV newvar (-i) x
        (FMultiply, Left i, Right (Neg x)) -> def $ MulVCV newvar (-i) x
        (FMultiply, Right (Pos x), Right (Pos y)) -> def $ MulVVV (Pos newvar) x y
        (FMultiply, Right (Neg x), Right (Pos y)) -> def $ MulVVV (Neg newvar) x y
        (FMultiply, Right (Pos x), Right (Neg y)) -> def $ MulVVV (Neg newvar) x y
        (FMultiply, Right (Neg x), Right (Neg y)) -> def $ MulVVV (Pos newvar) x y
        -- Division
        (FDivide, Left i1, Left i2) -> return (Left $ i1 `div` i2, body1 ++ body2)
        (FDivide, Right (Pos x), Left i) ->
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x i newvar
        (FDivide, Left i, Right (Pos x)) -> def $ DivVCV newvar i x
        (FDivide, Right (Neg x), Left i) -> 
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x (-i) newvar
        (FDivide, Left i, Right (Neg x)) -> def $ DivVCV newvar (-i) x
        (FDivide, Right (Pos x), Right (Pos y)) -> def $ DivVVV (Pos newvar) x y
        (FDivide, Right (Neg x), Right (Pos y)) -> def $ DivVVV (Neg newvar) x y
        (FDivide, Right (Pos x), Right (Neg y)) -> def $ DivVVV (Neg newvar) x y
        (FDivide, Right (Neg x), Right (Neg y)) -> def $ DivVVV (Pos newvar) x y
flatten (Just (Left j)) (AOp op e1 e2) = do
    (head1, body1) <- flatten Nothing e1
    (head2, body2) <- flatten Nothing e2
    -- Default return; should be used unless return is a constant
    let def a = return (Left j, a:body1 ++ body2)
    case (op, head1, head2) of
        -- Addition
        (FAdd, Left i1, Left i2) -> 
            if i1 + i2 /= j
            then lift $ Left "Different constants compared during 3ac generation (addition)"
            else return (Left $ i1 + i2, body1 ++ body2)
        (FAdd, Right (Pos x), Left i) -> def $ EVC x (j - i)
        (FAdd, Left i, Right (Pos x)) -> def $ EVC x (j - i)
        (FAdd, Right (Neg x), Left i) -> def $ EVC x (i - j)
        (FAdd, Left i, Right (Neg x)) -> def $ EVC x (i - j)
        (FAdd, Right (Pos x), Right (Pos y)) -> def $ AddCVV j x y
        (FAdd, Right (Neg x), Right (Pos y)) -> def $ AddVCV y j x
        (FAdd, Right (Pos x), Right (Neg y)) -> def $ AddVCV x j y
        (FAdd, Right (Neg x), Right (Neg y)) -> def $ AddCVV (-j) x y
        -- Subtraction
        (FSubtract, Left i1, Left i2) -> 
            if i1 - i2 /= j
            then lift $ Left "Different constants compared during 3ac generation (subtraction)"
            else return (Left $ i1 - i2, body1 ++ body2)
        (FSubtract, Right (Pos x), Left i) -> def $ EVC x (j + i)
        (FSubtract, Left i, Right (Pos x)) -> def $ EVC x (i - j)
        (FSubtract, Right (Neg x), Left i) -> def $ EVC x (-i - j)
        (FSubtract, Left i, Right (Neg x)) -> def $ EVC x (j - i)
        (FSubtract, Right (Pos x), Right (Pos y)) -> def $ AddVCV x j y
        (FSubtract, Right (Neg x), Right (Pos y)) -> def $ AddCVV (-j) x y
        (FSubtract, Right (Pos x), Right (Neg y)) -> def $ AddCVV j x y
        (FSubtract, Right (Neg x), Right (Neg y)) -> def $ AddVCV y j x
        -- Multiplication
        (FMultiply, Left i1, Left i2) -> 
            if i1 * i2 /= j
            then lift $ Left "Different constants compared during 3ac generation (multiplication)"
            else return (Left $ i1 * i2, body1 ++ body2)
        (FMultiply, Right (Pos x), Left i) -> 
            if i == 0
            then 
                if j /= 0
                then lift $ Left "Nonzero compared to multiplication by zero during 3ac generation"
                else def $ EVC x 0
            else def $ EVC x (j `div` i)
        (FMultiply, Left i, Right (Pos x)) -> 
            if i == 0
            then 
                if j /= 0
                then lift $ Left "Nonzero compared to multiplication by zero during 3ac generation"
                else def $ EVC x 0
            else def $ EVC x (j `div` i)
        (FMultiply, Right (Neg x), Left i) -> 
            if i == 0
            then 
                if j /= 0
                then lift $ Left "Nonzero compared to multiplication by zero during 3ac generation"
                else def $ EVC x 0
            else def $ EVC x (-j `div` i)
        (FMultiply, Left i, Right (Neg x)) -> 
            if i == 0
            then 
                if j /= 0
                then lift $ Left "Nonzero compared to multiplication by zero during 3ac generation"
                else def $ EVC x 0
            else def $ EVC x (-j `div` i)
        (FMultiply, Right (Pos x), Right (Pos y)) -> def $ MulCVV j x y
        (FMultiply, Right (Neg x), Right (Pos y)) -> def $ MulCVV (-j) x y
        (FMultiply, Right (Pos x), Right (Neg y)) -> def $ MulCVV (-j) x y
        (FMultiply, Right (Neg x), Right (Neg y)) -> def $ MulCVV j x y
        -- Division
        (FDivide, Left i1, Left i2) -> 
            if i1 `div` i2 /= j
            then lift $ Left "Different constants compared during 3ac generation (division)"
            else return (Left $ i1 `div` i2, body1 ++ body2)
        (FDivide, Right (Pos x), Left i) ->
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ EVC x (i * j)
        (FDivide, Left i, Right (Pos x)) -> def $ DivCCV j i x
        (FDivide, Right (Neg x), Left i) -> 
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ EVC x (-i * j)
        (FDivide, Left i, Right (Neg x)) -> def $ DivCCV j (-i) x
        (FDivide, Right (Pos x), Right (Pos y)) -> def $ DivCVV j x y
        (FDivide, Right (Neg x), Right (Pos y)) -> def $ DivCVV (-j) x y
        (FDivide, Right (Pos x), Right (Neg y)) -> def $ DivCVV (-j) x y
        (FDivide, Right (Neg x), Right (Neg y)) -> def $ DivCVV j x y
flatten (Just (Right (Pos newvar))) (AOp op e1 e2) = do
    (head1, body1) <- flatten Nothing e1
    (head2, body2) <- flatten Nothing e2
    -- Default return; should be used unless return is a constant
    let def a = do return (Right $ Pos newvar, a:body1 ++ body2)
    case (op, head1, head2) of
        -- Addition
        (FAdd, Left i1, Left i2) -> return (Left $ i1 + i2, EVC newvar (i1 + i2):body1 ++ body2)
        (FAdd, Right (Pos x), Left i) -> def $ AddVCV newvar i x
        (FAdd, Left i, Right (Pos x)) -> def $ AddVCV newvar i x
        (FAdd, Right (Neg x), Left i) -> def $ AddVCV newvar (-i) x
        (FAdd, Left i, Right (Neg x)) -> def $ AddVCV newvar (-i) x
        (FAdd, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Pos newvar) x y
        (FAdd, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Pos y) newvar x
        (FAdd, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Pos x) newvar y
        (FAdd, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Neg newvar) x y
        -- Subtraction
        (FSubtract, Left i1, Left i2) -> return (Left $ i1 - i2, EVC newvar (i1 - i2):body1 ++ body2)
        (FSubtract, Right (Pos x), Left i) -> def $ AddVCV newvar (-i) x
        (FSubtract, Left i, Right (Pos x)) -> def $ AddCVV i newvar x
        (FSubtract, Right (Neg x), Left i) -> def $ AddCVV (-i) newvar x
        (FSubtract, Left i, Right (Neg x)) -> def $ AddVCV newvar i x
        (FSubtract, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Pos x) newvar y
        (FSubtract, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Neg newvar) x y
        (FSubtract, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Pos newvar) x y
        (FSubtract, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Pos y) newvar x
        -- Multiplication
        (FMultiply, Left i1, Left i2) -> return (Left $ i1 * i2, EVC newvar (i1 * i2):body1 ++ body2)
        (FMultiply, Right (Pos x), Left i) -> def $ MulVCV newvar i x
        (FMultiply, Left i, Right (Pos x)) -> def $ MulVCV newvar i x
        (FMultiply, Right (Neg x), Left i) -> def $ MulVCV newvar (-i) x
        (FMultiply, Left i, Right (Neg x)) -> def $ MulVCV newvar (-i) x
        (FMultiply, Right (Pos x), Right (Pos y)) -> def $ MulVVV (Pos newvar) x y
        (FMultiply, Right (Neg x), Right (Pos y)) -> def $ MulVVV (Neg newvar) x y
        (FMultiply, Right (Pos x), Right (Neg y)) -> def $ MulVVV (Neg newvar) x y
        (FMultiply, Right (Neg x), Right (Neg y)) -> def $ MulVVV (Pos newvar) x y
        -- Division
        (FDivide, Left i1, Left i2) -> return (Left $ i1 `div` i2, EVC newvar (i1 `div` i2):body1 ++ body2)
        (FDivide, Right (Pos x), Left i) ->
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x i newvar
        (FDivide, Left i, Right (Pos x)) -> def $ DivVCV newvar i x
        (FDivide, Right (Neg x), Left i) -> 
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x (-i) newvar
        (FDivide, Left i, Right (Neg x)) -> def $ DivVCV newvar (-i) x
        (FDivide, Right (Pos x), Right (Pos y)) -> def $ DivVVV (Pos newvar) x y
        (FDivide, Right (Neg x), Right (Pos y)) -> def $ DivVVV (Neg newvar) x y
        (FDivide, Right (Pos x), Right (Neg y)) -> def $ DivVVV (Neg newvar) x y
        (FDivide, Right (Neg x), Right (Neg y)) -> def $ DivVVV (Pos newvar) x y
flatten (Just (Right (Neg newvar2))) (AOp op e1 e2) = do
    (head1, body1) <- flatten Nothing e1
    (head2, body2) <- flatten Nothing e2
    -- Default return; should be used unless return is a constant
    let def a = do return (Right $ Pos newvar2, a:body1 ++ body2)
    case (op, head1, head2) of
        -- Addition
        (FAdd, Left i1, Left i2) -> return (Left $ i1 + i2, EVC newvar2 (-i1 - i2):body1 ++ body2)
        (FAdd, Right (Pos x), Left i) -> def $ AddCVV (-i) newvar2 x
        (FAdd, Left i, Right (Pos x)) -> def $ AddCVV (-i) newvar2 x
        (FAdd, Right (Neg x), Left i) -> def $ AddCVV i newvar2 x
        (FAdd, Left i, Right (Neg x)) -> def $ AddCVV i newvar2 x
        (FAdd, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Neg newvar2) x y
        (FAdd, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Pos x) newvar2 y
        (FAdd, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Pos y) newvar2 x
        (FAdd, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Pos newvar2) x y
        -- Subtraction
        (FSubtract, Left i1, Left i2) -> return (Left $ i1 - i2, EVC newvar2 (-i1 + i2):body1 ++ body2)
        (FSubtract, Right (Pos x), Left i) -> def $ AddCVV i newvar2 x
        (FSubtract, Left i, Right (Pos x)) -> def $ AddVCV x i newvar2
        (FSubtract, Right (Neg x), Left i) -> def $ AddVCV x (-i) newvar2
        (FSubtract, Left i, Right (Neg x)) -> def $ AddCVV (-i) newvar2 x
        (FSubtract, Right (Pos x), Right (Pos y)) -> def $ AddVVV (Pos y) newvar2 x
        (FSubtract, Right (Neg x), Right (Pos y)) -> def $ AddVVV (Pos newvar2) x y
        (FSubtract, Right (Pos x), Right (Neg y)) -> def $ AddVVV (Neg newvar2) x y
        (FSubtract, Right (Neg x), Right (Neg y)) -> def $ AddVVV (Pos x) newvar2 y
        -- Multiplication
        (FMultiply, Left i1, Left i2) -> return (Left $ i1 * i2, EVC newvar2 (-i1 * i2):body1 ++ body2)
        (FMultiply, Right (Pos x), Left i) -> def $ MulVCV newvar2 (-i) x
        (FMultiply, Left i, Right (Pos x)) -> def $ MulVCV newvar2 (-i) x
        (FMultiply, Right (Neg x), Left i) -> def $ MulVCV newvar2 i x
        (FMultiply, Left i, Right (Neg x)) -> def $ MulVCV newvar2 i x
        (FMultiply, Right (Pos x), Right (Pos y)) -> def $ MulVVV (Neg newvar2) x y
        (FMultiply, Right (Neg x), Right (Pos y)) -> def $ MulVVV (Pos newvar2) x y
        (FMultiply, Right (Pos x), Right (Neg y)) -> def $ MulVVV (Pos newvar2) x y
        (FMultiply, Right (Neg x), Right (Neg y)) -> def $ MulVVV (Neg newvar2) x y
        -- Division
        (FDivide, Left i1, Left i2) -> return (Left $ i1 `div` i2, EVC newvar2 (-i1 `div` i2):body1 ++ body2)
        (FDivide, Right (Pos x), Left i) ->
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x (-i) newvar2
        (FDivide, Left i, Right (Pos x)) -> def $ DivVCV newvar2 (-i) x
        (FDivide, Right (Neg x), Left i) -> 
            if i == 0
            then lift $ Left "Division by zero encountered during 3ac generation"
            else def $ MulVCV x i newvar2
        (FDivide, Left i, Right (Neg x)) -> def $ DivVCV newvar2 i x
        (FDivide, Right (Pos x), Right (Pos y)) -> def $ DivVVV (Neg newvar2) x y
        (FDivide, Right (Neg x), Right (Pos y)) -> def $ DivVVV (Pos newvar2) x y
        (FDivide, Right (Pos x), Right (Neg y)) -> def $ DivVVV (Pos newvar2) x y
        (FDivide, Right (Neg x), Right (Neg y)) -> def $ DivVVV (Neg newvar2) x y

-- Note: The way this works, the second expression will have, potentially, fewer constraints
-- as the variable in the first expression can be shared with the second. This means that
-- equations without operations on one side will be smaller if the non-op is on the left side.
-- For example, x * (x - 1) = 0 will be bigger than 0 = x * (x - 1)
flattenEq :: Clause -> FlatM [ThreeAddressCode]
flattenEq (ClEq e1 e2) = do
    (hd1, bdy1) <- flatten Nothing e1
    (_, bdy2) <- flatten (Just hd1) e2
    return $ bdy1 ++ bdy2

flattenConstraints :: Constraints -> FlatM [ThreeAddressCode]
flattenConstraints = foldr ((<*>) . ((++) <$>) . flattenEq) (return [])
