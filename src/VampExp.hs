{-# LANGUAGE RankNTypes #-}

module VampExp
    ( Variable, Pat(..), InfixOp(..), Expr(..), LetBinding(..), Module(..), Definition(..)
    ) where

import qualified Data.Map as Map
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Reader
import Constraints
import Core

data Module = Module [Variable] [Definition] [Expr]

data LetBinding = LetBinding Pat Expr deriving (Show, Eq)
newtype Definition = Definition LetBinding

data Pat
    = Unit
    | Nil
    | Pair Pat Pat
    | Cons Pat Pat
    | ConstP Integer
    | VarPat Variable
    deriving (Show, Eq)

data InfixOp
    = Divide
    | DivideZ
    | Multiply
    | Add
    | Subtract
    | Equal
    | And
    | Exponentiate
    | IntDivide
    | Modulo
    deriving (Show, Eq)

data Expr
    = UnitE
    | NilE
    | PairE Expr Expr
    | ConsE Expr Expr
    | Infix InfixOp Expr Expr
    | Negate Expr
    | Application Expr Expr
    | ConstantE Integer
    | VarExpr Variable
    | FunctionE [Pat] Expr
    | LetBindingE LetBinding Expr
    | Intrinsic String
    deriving (Show, Eq)

type CtxM v x = Map.Map VariableId v -> x

-- Note, the basic premise of the translation is that every expression is truned into
-- a CtxM v (CoreP f v) by translateExp. Everything else should be
-- handled by functions that work directly with CtxM v (CoreP f v)
-- I didn't do this with foldDefs because it makes things a little nicer.

-- Note: This is less restrictive than it could hypothetically be
--       does not actually err when invalid matches to constants, etc, occur
patternAccessors :: v -> Pat -> [(Variable, CoreP f v)]
patternAccessors _ Unit = []
patternAccessors _ Nil = []
patternAccessors _ (ConstP _) = []
patternAccessors v (Pair pat1 pat2) = map (second CTl) (patternAccessors v pat1) ++ map (second CTl) (patternAccessors v pat2)
patternAccessors v (Cons pat1 pat2) = map (second CFst) (patternAccessors v pat1) ++ map (second CSnd) (patternAccessors v pat2)
patternAccessors v (VarPat var) = [(var, CVar var (Just v))]

-- Fold over the pattern accessors, turning, for example,
-- 'let (x, y, z) = e in ?' into '\u (\x (\y (\z v) u.3) u.2) u.3'
translatePat :: Pat -> CtxM v (CoreP f v) -> CtxM v (CoreP f v)
translatePat pat expr ctx = CLam Nothing Nothing $ \v -> foldr mkBnd expr (reverse $ patternAccessors v pat) ctx
    where
    -- Take a variable name and binds a real variable to it
    bndArg var expr0 ctx0 = CLam (Just $ varid var) Nothing $ \v -> expr0 (Map.insert (varid var) v ctx0)
    -- Takes a let v := a in e and turns it into '(\v. e) a'
    mkBnd (var, acsr) expr0 = flip CApp acsr <$> bndArg var expr0

-- Given 'let (x, y, z) = e in v' turn into '(\u (\x (\y (\z v) u.3) u.2) u.3) v'
patBnd :: Pat -> CtxM v (CoreP f v) -> CtxM v (CoreP f v) -> CtxM v (CoreP f v)
patBnd pat lt body = liftA2 CApp (translatePat pat body) lt

foldDefs :: Num f => [Definition] -> Expr -> CtxM v (CoreP f v)
foldDefs [] body = translateExp body
foldDefs (Definition (LetBinding pat expr) : ds) body = 
    patBnd pat (translateExp expr) (foldDefs ds body)

translateExp :: Num f => Expr -> CtxM v (CoreP f v)
translateExp UnitE = return CUnit
translateExp NilE = return CNil
translateExp (PairE e1 e2) = liftA2 CPair (translateExp e1) (translateExp e2)
translateExp (ConsE e1 e2) = liftA2 CCons (translateExp e1) (translateExp e2)
translateExp (Infix op e1 e2) = translateInfix op e1 e2
translateExp (Negate e) = CNeg <$> translateExp e
translateExp (Application e1 e2) = liftA2 CApp (translateExp e1) (translateExp e2)
translateExp (ConstantE int) = return $ CConst (fromInteger int)
translateExp (VarExpr var@(Variable _ i)) = 
    ask >>= \ctx ->
    case Map.lookup i ctx of
        Just v  -> return $ CVar var (Just v)
        Nothing -> return $ CVar var Nothing
translateExp (FunctionE pats expr) = foldr translatePat (translateExp expr) (reverse pats)
translateExp (LetBindingE (LetBinding pat e1) e2) = 
    patBnd pat (translateExp e1) (translateExp e2)
translateExp (Intrinsic s) = return $ CIntrinsic s

translateInfix :: Num f => InfixOp -> Expr -> Expr -> CtxM v (CoreP f v)
translateInfix op e1 e2 =
    let f x = liftA2 x (translateExp e1) (translateExp e2)
    in f (case op of
            Divide -> COp ADivide
            DivideZ -> COp ADivideZ
            Multiply -> COp AMultiply
            Add -> COp AAdd
            Subtract -> COp ASubtract
            Equal -> CEq
            And -> CAnd
            Exponentiate -> COp AExponentiate
            IntDivide -> COp AIntDivide
            Modulo -> COp AModulo
          )

translateToCore :: Num f => Module -> Core f
translateToCore (Module _ defs exprs) = Core $ foldDefs defs (foldr1 (Infix And) exprs) Map.empty