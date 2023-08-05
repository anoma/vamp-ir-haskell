{-# LANGUAGE RankNTypes #-}

module Core
    ( ArithOp(..), Core(..), CoreP(..),
    ) where

import Constraints
import Control.Applicative
import Control.Monad.State
import qualified Data.Map as M

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
    | CFresh [CoreP v]
    | CLam (Maybe VariableId) (Maybe Int) (v -> CoreP v)
    | CApp (CoreP v) (CoreP v)
    | COp ArithOp (CoreP v) (CoreP v)
    | CConst Integer
    | CNeg (CoreP v)
    | CIntrinsic String

newtype Core = Core { unCore :: forall a . CoreP a }

data CallNumTree
    = CaLeaf
    | CaBranch CallNumTree CallNumTree
    | CaLam Int CallNumTree

-- Number of times a variable id appears under its binder
callNumbers :: Core -> CallNumTree
callNumbers = snd . go . unCore where
    go :: CoreP () -> (M.Map VariableId Int, CallNumTree)
    go expr = case expr of
        (CVar var _) -> (M.fromList [(varid var, 1)], CaLeaf)
        (CEq e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (CAnd e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (CPair e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (CCons e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (CApp e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (COp _ e1 e2) -> 
            let (m1, e1') = go e1
                (m2, e2') = go e2
            in (M.unionWith (+) m1 m2, CaBranch e1' e2')
        (CFst e1) -> 
            let (m1, e1') = go e1
            in (m1, e1')
        (CSnd e1) -> 
            let (m1, e1') = go e1
            in (m1, e1')
        (CHd e1) -> 
            let (m1, e1') = go e1
            in (m1, e1')
        (CTl e1) -> 
            let (m1, e1') = go e1
            in (m1, e1')
        (CNeg e1) -> 
            let (m1, e1') = go e1
            in (m1, e1')
        (CLam Nothing _ f) -> 
            let (m1, e1') = go (f ())
            in (m1, CaLam 0 e1')
        (CLam (Just i) _ f) -> 
            let (m1, e1') = go (f ())
                m' = M.delete i m1
            in (m', CaLam (m1 M.! i) e1')
        CNil -> (M.empty, CaLeaf)
        CUnit -> (M.empty, CaLeaf)
        (CFresh _) -> (M.empty, CaLeaf)
        (CIntrinsic _) -> (M.empty, CaLeaf)
        (CConst _) -> (M.empty, CaLeaf)

-- Is there a more direct way to do this?
callDecorate :: Core -> Core
callDecorate exp = Core $ go (unCore exp) (callNumbers exp) where
    go :: CoreP v -> CallNumTree -> CoreP v
    go expr ctn = case (expr, ctn) of
        (b, CaLeaf) -> b
        (CFst e1, c) -> CFst $ go e1 c
        (CSnd e1, c) -> CSnd $ go e1 c
        (CHd e1, c) -> CHd $ go e1 c
        (CTl e1, c) -> CTl $ go e1 c
        (CNeg e1, c) -> CNeg $ go e1 c

        (CEq e1 e2, CaBranch c1 c2) -> CEq (go e1 c1) (go e2 c2)
        (CAnd e1 e2, CaBranch c1 c2) -> CAnd (go e1 c1) (go e2 c2)
        (CPair e1 e2, CaBranch c1 c2) -> CPair (go e1 c1) (go e2 c2)
        (CCons e1 e2, CaBranch c1 c2) -> CCons (go e1 c1) (go e2 c2)
        (CApp e1 e2, CaBranch c1 c2) -> CApp (go e1 c1) (go e2 c2)
        (COp op e1 e2, CaBranch c1 c2) -> COp op (go e1 c1) (go e2 c2)

        (CLam i _ f, CaLam n c) -> CLam i (Just n) (\v -> go (f v) c)
        _ -> CConst 0 -- Default that should never occur

newtype Normalized = Normalized {unNormalized :: CoreP Normalized}

data RoughType = RConstraint | RElement | RArithExp | RFresh | ROther deriving (Eq)
roughType :: CoreP v -> RoughType
roughType expr = case expr of
    CVar _ _-> RElement
    CEq _ _ -> RConstraint
    CAnd _ _ -> RConstraint
    CUnit -> ROther
    CPair _ _ -> ROther
    CFst _ -> ROther
    CSnd _ -> ROther
    CCons _ _ -> ROther
    CNil -> ROther
    CHd _ -> ROther
    CTl _ -> ROther
    CFresh _ -> RFresh
    CLam {} -> ROther
    CApp _ _ -> ROther
    COp {} -> RArithExp
    CNeg _ -> RArithExp
    CConst _ -> RElement
    CIntrinsic _ -> ROther

-- State contains the next free variable name
-- And a mapping from variables to normalzied terms
type EvalM x = StateT (VariableId, M.Map VariableId (CoreP Normalized)) (Either String) x

normalize :: CoreP Normalized -> [CoreP Normalized] -> EvalM (CoreP Normalized)
normalize expr l = case expr of
    CVar var Nothing -> case l of
        [] -> return $ CVar var Nothing
        _ -> lift $ Left "Cannot apply argument to free variable"
    CVar _ (Just r) -> case l of
        [] -> return $ unNormalized r
        _ -> normalize (unNormalized r) l
    CEq e1 e2 -> case l of
        [] -> liftA2 CEq (normalize e1 []) (normalize e2 [])
        _ -> lift $ Left "Cannot apply argument to equation"
    CAnd e1 e2 -> case l of
        [] -> liftA2 CAnd (normalize e1 []) (normalize e2 [])
        _ -> lift $ Left "Cannot apply argument to conjunction"
    CUnit -> case l of
        [] -> return CUnit
        _ -> lift $ Left "Cannot apply argument to unit"
    CPair e1 e2 -> case l of
        [] -> liftA2 CPair (normalize e1 []) (normalize e2 [])
        _ -> lift $ Left "Cannot apply argument to pair"
    CFst (CPair a _) -> case l of
        [] -> return a
        _ -> normalize a l
    CFst _ -> lift $ Left "Cannot take first element of non-pair"
    CSnd (CPair _ b) -> case l of
        [] -> return b
        _ -> normalize b l
    CSnd _ -> lift $ Left "Cannot take second element of non-pair"
    CCons e1 e2 -> case l of
        [] -> liftA2 CCons (normalize e1 []) (normalize e2 [])
        _ -> lift $ Left "Cannot apply argument to list"
    CNil -> return CNil
    CHd (CCons a _) -> case l of
        [] -> return a
        _ -> normalize a l
    CHd CNil -> lift $ Left "Cannot take head of empty list"
    CHd _ -> lift $ Left "Cannot take head of non list"
    CTl (CCons _ b) -> case l of
        [] -> return b
        _ -> normalize b l
    CTl CNil -> lift $ Left "Cannot take tail of empty list"
    CTl _ -> lift $ Left "Cannot take tail of non list"
    CFresh s -> case l of
        [] -> return $ CFresh s
        _ -> lift $ Left "Cannot apply argument to fresh"
    CLam mi calls f -> case l of
        [] -> return $ CLam mi calls f
        (x:xs) -> 
            case calls of
                Nothing -> normalize (f (Normalized x)) xs
                Just i -> 
                    let rt = roughType x in
                    if (i <= 1 || rt /= RArithExp) && rt /= RFresh
                    then normalize (f (Normalized x)) xs
                    else do
                        (newid, _) <- get
                        let newvar = newVar newid
                        modify (\(nid, mp) -> (nid+1, M.insert nid x mp))
                        normalize (f $ Normalized $ CVar newvar Nothing) xs
    CApp e1 e2 -> normalize e2 [] >>= normalize e1 . (:l)
    COp op e1 e2 -> case l of
        [] -> liftA2 (COp op) (normalize e1 []) (normalize e2 [])
        _ -> lift $ Left "Cannot apply argument to an arithmetic term"
    CNeg e -> case l of
        [] -> CNeg <$> normalize e []
        _ -> lift $ Left "Cannot apply argument to a negated term"
    CConst i -> case l of
        [] -> return $ CConst i
        _ -> lift $ Left "Cannot apply argument to a constant"
    CIntrinsic name -> case name of
        "iter" -> case l of
            (CConst i:s:z:l') ->
              if i < 0
              then lift $ Left "First input to iter must be nonegative"
              else
                if i == 0
                then normalize z l'
                else normalize s (expr:CConst (i - 1):z:s:l')
            (_:_:_:_) -> lift $ Left "First input to iter must be constant"
            _ -> lift $ Left "At least three arguments must be applied to evaluate iter"
        "fold" -> case l of
            (CNil:_:cn:l') -> normalize cn l'
            (CCons x xs:cc:cn:l') -> normalize cc (x:expr:xs:cc:cn:l')
            (_:_:_:_) -> lift $ Left "First input to fold must be a list"
            _ -> lift $ Left "At least three arguments must be applied to evaluate fold"
        _ -> lift $ Left "Unknown intrinsic"

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
    CFresh s -> AFresh <$> forM s evala
    CLam {} -> Left "Lambda expressions cannot be interpreted as arithmetic expressions"
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
    CLam {} -> Left "Lambda expressions cannot represent constraints"
    CApp _ _ -> Left "Impossible application"
    COp {} -> Left "Arithmetic expressions cannot represent constraints"
    CNeg _ -> Left "Negated expressions cannot represent constraints"
    CConst _ -> Left "Constants cannot represent constraints"
    CIntrinsic _ -> Left "Impossible intrinsic"

run :: VariableId -> Core -> Either String (Constraints, VariableId)
run i c = do
    (norm, (mid, mdefs)) <- runStateT (normalize (unCore (callDecorate c)) []) (i, M.empty)
    norm' <- evalc norm
    let mdefs' = map (\(x, y) -> CEq (CVar (newVar x) Nothing) y) $ M.toList mdefs
    mcons <- forM mdefs' evalc
    return (concat $ norm':mcons, mid)

eval :: VariableId -> Core -> Either String Constraints
eval i c = evalStateT (normalize (unCore (callDecorate c)) []) (i, M.empty) >>= evalc