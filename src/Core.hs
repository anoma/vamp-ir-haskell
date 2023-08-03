{-# LANGUAGE RankNTypes #-}

module Core
    ( ArithOp(..), Core(..), CoreP(..),
    ) where

import Constraints
import Control.Applicative

data ArithOp
    = ADivide
    | ADivideZ
    | AMultiply
    | AAdd
    | ASubtract
    | AExponentiate
    | AIntDivide
    | AModulo
    deriving (Show, Eq)

data CoreP v
    = CVar Variable (Maybe v)
    | CEq (CoreP v) (CoreP v)
    | CAnd (CoreP v) (CoreP v)
    | CUnit
    | CPair (CoreP v) (CoreP v) | CFst (CoreP v) | CSnd (CoreP v)
    | CCons (CoreP v) (CoreP v) | CNil | CHd (CoreP v) | CTl (CoreP v)
    | CFresh Sig
    | CLam (v -> CoreP v)
    | CApp (CoreP v) (CoreP v)
    | COp ArithOp (CoreP v) (CoreP v)
    | CConst Integer
    | CNeg (CoreP v)
    | CIntrinsic String

newtype Core = Core { unCore :: forall a . CoreP a }

newtype Normalized = Normalized {unNormalized :: CoreP Normalized}

normalize :: CoreP Normalized -> [CoreP Normalized] -> Either String (CoreP Normalized)
normalize expr l = case expr of
    CVar var Nothing -> case l of
        [] -> return $ CVar var Nothing
        _ -> Left "Cannot apply argument to free variable"
    CVar _ (Just r) -> case l of
        [] -> return $ unNormalized r
        _ -> normalize (unNormalized r) l
    CEq e1 e2 -> case l of
        [] -> liftA2 CEq (normalize e1 []) (normalize e2 [])
        _ -> Left "Cannot apply argument to equation"
    CAnd e1 e2 -> case l of
        [] -> liftA2 CAnd (normalize e1 []) (normalize e2 [])
        _ -> Left "Cannot apply argument to conjunction"
    CUnit -> case l of
        [] -> return CUnit
        _ -> Left "Cannot apply argument to unit"
    CPair e1 e2 -> case l of
        [] -> liftA2 CPair (normalize e1 []) (normalize e2 [])
        _ -> Left "Cannot apply argument to pair"
    CFst (CPair a _) -> case l of
        [] -> return a
        _ -> normalize a l
    CFst _ -> Left "Cannot take first element of non-pair"
    CSnd (CPair _ b) -> case l of
        [] -> return b
        _ -> normalize b l
    CSnd _ -> Left "Cannot take second element of non-pair"
    CCons e1 e2 -> case l of
        [] -> liftA2 CCons (normalize e1 []) (normalize e2 [])
        _ -> Left "Cannot apply argument to list"
    CNil -> return CNil
    CHd (CCons a _) -> case l of
        [] -> return a
        _ -> normalize a l
    CHd CNil -> Left "Cannot take head of empty list"
    CHd _ -> Left "Cannot take head of non list"
    CTl (CCons _ b) -> case l of
        [] -> return b
        _ -> normalize b l
    CTl CNil -> Left "Cannot take tail of empty list"
    CTl _ -> Left "Cannot take tail of non list"
    CFresh s -> case l of
        [] -> return $ CFresh s
        _ -> Left "Cannot apply argument to fresh"
    CLam f -> case l of
        [] -> return $ CLam f
        (x:xs) -> normalize (f (Normalized x)) xs
    CApp e1 e2 -> normalize e2 [] >>= normalize e1 . (:l)
    COp op e1 e2 -> case l of
        [] -> liftA2 (COp op) (normalize e1 []) (normalize e2 [])
        _ -> Left "Cannot apply argument to an arithmetic term"
    CNeg e -> case l of
        [] -> CNeg <$> normalize e []
        _ -> Left "Cannot apply argument to a negated term"
    CConst i -> case l of
        [] -> return $ CConst i
        _ -> Left "Cannot apply argument to a constant"
    CIntrinsic name -> case name of
        "iter" -> case l of
            (CConst i:s:z:l') ->
              if i < 0
              then Left "First input to iter must be nonegative"
              else
                if i == 0
                then normalize z l'
                else normalize s (expr:CConst (i - 1):z:s:l')
            (_:_:_:_) -> Left "First input to iter must be constant"
            _ -> Left "At least three arguments must be applied to evaluate iter"
        "fold" -> case l of
            (CNil:_:cn:l') -> normalize cn l'
            (CCons x xs:cc:cn:l') -> normalize cc (x:expr:xs:cc:cn:l')
            (_:_:_:_) -> Left "First input to fold must be a list"
            _ -> Left "At least three arguments must be applied to evaluate fold"
        _ -> Left "Unknown intrinsic"

toFieldOp :: ArithOp -> Either String FieldOp
toFieldOp AAdd = Right FAdd
toFieldOp ASubtract = Right FSubtract
toFieldOp AMultiply = Right FMultiply
toFieldOp ADivide = Right FDivide
toFieldOp _ = Left "Not a field operation"

evala :: CoreP Normalized -> Either String ArithExp
evala expr = case expr of
    CVar var Nothing -> return $ AVar var
    CVar _ (Just _) -> Left "Impossible wrapped variable"
    CEq _ _ -> Left "Equations cannot be interpreted as arithmetic expressions"
    CAnd _ _ -> Left "Conjunctions cannot be interpreted as arithmetic expressions"
    CUnit -> Left "Units cannot be interpreted as arithmetic expressions"
    CPair _ _ -> Left "Pairs cannot be interpreted as arithmetic expressions"
    CFst _ -> Left "Impossible first projection"
    CSnd _ -> Left "Impossible second projection"
    CCons _ _ -> Left "Nonempty lists cannot be interpreted as arithmetic expressions"
    CNil -> Left "Empty lists cannot be interpreted as arithmetic expressions"
    CHd _ -> Left "Impossible head projection"
    CTl _ -> Left "Impossible tail projection"
    CFresh s -> return $ AFresh s
    CLam _ -> Left "Lambda expressions cannot be interpreted as arithmetic expressions"
    CApp _ _ -> Left "Impossible function application"
    COp op e1 e2 -> AOp <$> toFieldOp op <*> evala e1 <*> evala e2
    CNeg e -> ANeg <$> evala e 
    CConst i -> return $ AConst i
    CIntrinsic _ -> Left "Impossible intrinsic"

evalc :: CoreP Normalized -> Either String Constraints
evalc expr = case expr of
    CVar _ _ -> Left "Variables cannot stand for constraints"
    CEq (CPair a1 b1) (CPair a2 b2) -> liftA2 (++) (evalc (CEq a1 b1)) (evalc (CEq a2 b2))
    CEq (CPair _ _) _ -> Left "Pairs must be compared to pairs"
    CEq _ (CPair _ _) -> Left "Pairs must be compared to pairs"
    CEq (CCons a1 b1) (CCons a2 b2) -> liftA2 (++) (evalc (CEq a1 b1)) (evalc (CEq a2 b2))
    CEq (CCons _ _) _ -> Left "Nonempty lists must be compared to nonempty lists"
    CEq _ (CCons _ _) -> Left "Nonempty lists must be compared to nonempty lists"
    CEq CNil CNil -> return []
    CEq CNil _ -> Left "Empty lists must be compared to empty lists"
    CEq _ CNil -> Left "Empty lists must be compared to empty lists"
    CEq CUnit CUnit -> return []
    CEq CUnit _ -> Left "Units must be compared to Units"
    CEq _ CUnit -> Left "Units must be compared to Units"
    CEq e1 e2 -> liftA2 (((:[]) .) . ClEq) (evala e1) (evala e2)
    CAnd e1 e2 -> liftA2 (++) (evalc e1) (evalc e2)
    CUnit -> return []
    CPair _ _ -> Left "Pairs cannot be interpreted as constraints"
    CFst _ -> Left "Impossible first projection"
    CSnd _ -> Left "Impossible secpmd projection"
    CCons _ _ -> Left "Nonempty lists cannot be interpreted as constraints"
    CNil -> Left "Empty lists cannot be interpreted as constraints"
    CHd _ -> Left "Impossible head projection"
    CTl _ -> Left "Impossible tail projection"
    CFresh _ -> Left "Fresh expressions cannot stand for constraints"
    CLam _ -> Left "Lambda expressions cannot represent constraints"
    CApp _ _ -> Left "Impossible application"
    COp {} -> Left "Arithmetic expressions cannot represent constraints"
    CNeg _ -> Left "Negated expressions cannot represent constraints"
    CConst _ -> Left "Constants cannot represent constraints"
    CIntrinsic _ -> Left "Impossible intrinsic"

eval :: Core -> Either String Constraints
eval (Core c) = normalize c [] >>= evalc