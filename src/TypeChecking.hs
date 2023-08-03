{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

-- Note: This is heavily based on "Implementing Hindley-Milner with the unification-fd library" by Brent Yorgey
module TypeChecking
    ( TypeF(..), Type, Poly(..), inferPolytype, checkType
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Functor.Identity
import qualified Data.Map                   as M
import           Data.Maybe
import           Prelude                    hiding (lookup)
import           Data.Functor

import           Control.Unification        
import           Control.Unification.IntVar
import qualified Data.Set                   as S
import           GHC.Generics               (Generic1)
import           Data.Foldable              (fold)
import           Data.Functor.Fixedpoint

import Constraints
import Core

deriving instance Ord IntVar

instance Fallible TypeF IntVar String where
  occursFailure   i trm = "Infinite unification " ++ show i ++ " " ++ show trm
  mismatchFailure t1 t2 = "Mismatch between " ++ show t1 ++ " " ++ show t2

type VarName = String
data TypeF r = TypeVarF VarName | FieldElemF | ConstraintF | UnitF | ProductF r r | FunF r r | ListF r
   deriving (Show, Eq, Functor, Foldable, Traversable, Generic1, Unifiable)
type UType = UTerm TypeF IntVar

data Poly t = Forall [VarName] t
  deriving (Eq, Show, Functor)
type UPolytype = Poly UType

type Ctx = M.Map VariableId UPolytype
type Infer = ReaderT Ctx (ExceptT String (IntBindingT TypeF Identity))

fresh :: Infer UType
fresh = UVar <$> lift (lift freeVar)

-- Note: The reason this looks complicated is because it needs to handle quantified types.
-- If we have a function f : X -> (Y -> X) -> X, then X and Y need to be assigned new identities for each call.
lookup :: VariableId -> Infer UType
lookup x = do
  ctx <- ask
  maybe (throwError $ "Unbound Variable " ++ show x)
        instantiate
        (M.lookup x ctx)
  where
  instantiate (Forall xs uty) = do
      xs' <- mapM (const fresh) xs
      return $ substU (M.fromList (zip (map Left xs) xs')) uty

substU :: M.Map (Either VarName IntVar) UType -> UType -> UType
substU m (UVar v) = fromMaybe (UVar v) (M.lookup (Right v) m)
substU m (UTerm (TypeVarF v)) = fromMaybe (UTerm $ TypeVarF v) (M.lookup (Left v) m)
substU m (UTerm t) = UTerm (fmap (substU m) t)

check :: CoreP UType -> UType -> Infer ()
check e ty = do
  ty' <- infer e
  _ <- lift $ ty =:= ty'
  return ()

infer :: CoreP UType -> Infer UType
infer expr = case expr of
    CVar var Nothing -> lookup $ varid var
    CVar _ (Just ty) -> return ty
    CEq e1 e2 -> check e1 (UTerm FieldElemF) >> check e2 (UTerm FieldElemF) >> return (UTerm ConstraintF)
    CAnd e1 e2 -> check e1 (UTerm ConstraintF) >> check e2 (UTerm ConstraintF) >> return (UTerm ConstraintF)
    CUnit -> return (UTerm UnitF)
    CPair e1 e2 -> liftM2 ((UTerm .) . ProductF) (infer e1) (infer e2)
    CFst e -> do
        pairTy <- infer e
        fstTy <- fresh
        sndTy <- fresh
        _ <- lift $ pairTy =:= UTerm (ProductF fstTy sndTy)
        return fstTy
    CSnd e -> do
        pairTy <- infer e
        fstTy <- fresh
        sndTy <- fresh
        _ <- lift $ pairTy =:= UTerm (ProductF fstTy sndTy)
        return sndTy
    CCons e1 e2 -> do
        elmTy <- infer e1
        lstTy <- infer e2
        _ <- lift $ lstTy =:= UTerm (ListF elmTy)
        return lstTy
    CNil -> fresh <&> (UTerm . ListF)
    CHd e -> do
        argTy <- infer e
        resTy <- fresh
        _ <- lift $ argTy =:= UTerm (ListF resTy)
        return resTy
    CTl e -> do
        argTy <- infer e
        resTy <- fresh
        _ <- lift $ argTy =:= UTerm (ListF resTy)
        return argTy
    CFresh _ -> return $ UTerm FieldElemF -- Note: Should this be generalized?
    CLam f -> do
        argTy <- fresh
        resTy <- infer (f argTy)
        return $ UTerm $ FunF argTy resTy
    CApp e1 e2 -> do
        funTy <- infer e1
        argTy <- infer e2
        resTy <- fresh
        _ <- lift $ funTy =:= UTerm (FunF argTy resTy)
        return resTy
    COp _ e1 e2 -> check e1 (UTerm FieldElemF) >> check e2 (UTerm FieldElemF) >> return (UTerm FieldElemF)
    CConst _ -> return $ UTerm FieldElemF
    CNeg e -> check e (UTerm FieldElemF) >> return (UTerm FieldElemF)
    CIntrinsic str -> case str of
        "iter" -> do
            baseTy <- fresh
            return $ 
                UTerm $ FunF 
                  (UTerm FieldElemF) 
                (UTerm $ FunF 
                  baseTy 
                (UTerm $ FunF 
                  (UTerm $ FunF baseTy baseTy) 
                  baseTy))
        "fold" -> do
            baseTy <- fresh
            recTy <- fresh
            return $ 
                UTerm $ FunF 
                  (UTerm $ ListF recTy)
                (UTerm $ FunF 
                  (UTerm $ FunF recTy (UTerm $ FunF baseTy baseTy))
                (UTerm $ FunF 
                  baseTy
                  baseTy))
        _ -> throwError $ "Unknown intrinsic " ++ str 

-- The rest of this just takes a term with unification variables and turns
-- those variables into type variables.
class FreeVars a where
  freeVars :: a -> Infer (S.Set (Either VarName IntVar))
instance FreeVars UType where
  freeVars ut = do
    fuvs <- fmap (S.fromList . map Right) . lift . lift $ getFreeVars ut
    let ftvs = freeTypeVars ut
    return $ fuvs `S.union` ftvs
    where
      freeTypeVars (UVar _)  = S.empty
      freeTypeVars (UTerm t) = handleType (fmap freeTypeVars t)

      handleType (TypeVarF x) = S.singleton (Left x)
      handleType f            = fold f
instance FreeVars UPolytype where
  freeVars (Forall xs ut) = (S.\\ S.fromList (map Left xs)) <$> freeVars ut
instance FreeVars Ctx where
  freeVars = fmap S.unions . mapM freeVars . M.elems

-- How to improve this?
mkVarName nm (IntVar v) = nm ++ show (v + (maxBound :: Int) + 1)

generalize :: UType -> Infer UPolytype
generalize uty = do
  uty' <- lift $ applyBindings uty
  ctx <- ask
  tmfvs  <- freeVars uty'
  ctxfvs <- freeVars ctx
  let fvs = S.toList $ tmfvs S.\\ ctxfvs
      xs  = map (either id (mkVarName "a")) fvs
  return $ Forall xs (substU (M.fromList (zip fvs (map (UTerm . TypeVarF) xs))) uty')

type Type = Fix TypeF
type Polytype  = Poly Type

runInfer :: Infer a -> Either String a
runInfer = runIdentity . evalIntBindingT . runExceptT . flip runReaderT M.empty

genpoly :: Infer UType -> Infer Polytype
genpoly = fmap (fmap (fromJust . freeze)) . generalize <=< (>>= (lift . applyBindings))

inferPolytype :: Core -> Either String Polytype
inferPolytype = runInfer . genpoly . infer . unCore

checkType :: Core -> Type -> Either String ()
checkType expr = runInfer . check (unCore expr) . unfreeze
