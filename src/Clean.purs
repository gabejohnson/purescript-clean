module Clean
  ( Scheme
  , Type
  , TypeInferenceEnv
  , TypeInferenceState
  , runTypeInference
  , typeInference
  ) where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Except.Trans (ExceptT, runExceptT, throwError)
import Control.Monad.Reader.Trans (ReaderT, runReaderT)
import Control.Monad.State.Trans (StateT, get, put, runStateT)
import Data.Array (fromFoldable, zip)
import Data.Either (Either)
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

import Clean.Expressions (Exp(..), Lit(..))

class Types a where
  getFreeTypeVars :: a -> Set.Set String
  applySubst :: Subst -> a -> a

instance typesArray :: Types a => Types (Array a) where
  getFreeTypeVars l = foldr Set.union Set.empty (map getFreeTypeVars l)
  applySubst s = map (applySubst s)

-- Types
data Type = TVar String
          | TNumber
          | TBoolean
          | TString
          | TFun Type Type
derive instance eqType :: Eq Type
derive instance ordType :: Ord Type

instance typesType :: Types Type where
  getFreeTypeVars = case _ of
    TVar n     -> Set.singleton n
    TFun t1 t2 -> getFreeTypeVars t1 `Set.union` getFreeTypeVars t2
    _          -> Set.empty

  applySubst s = case _ of
    TVar n     -> fromMaybe (TVar n) $ Map.lookup n s
    TFun t1 t2 -> TFun (applySubst s t1) (applySubst s t2)
    t          -> t

-- Type schemes (type constructors?)
data Scheme = Scheme (Array String) Type

instance typesScheme :: Types Scheme where
  getFreeTypeVars (Scheme vars t) = getFreeTypeVars t `Set.difference` Set.fromFoldable vars
  applySubst s (Scheme vars t) = Scheme vars $ applySubst (foldr Map.delete s vars) t

-- Type substitutions
type Subst = Map.Map String Type

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = map (applySubst s1) s2 `Map.union` s1

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

instance typesTypeEnv :: Types TypeEnv where
  getFreeTypeVars (TypeEnv env) = getFreeTypeVars $ fromFoldable (Map.values env)
  applySubst s (TypeEnv env) = TypeEnv $ map (applySubst s) env

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toUnfoldable $ getFreeTypeVars t `Set.difference` getFreeTypeVars env

data TypeInferenceEnv = TypeInferenceEnv
data TypeInferenceState = TypeInferenceState { supply :: Int
                                             , subst :: Subst
                                             }

type TypeInference a
  = forall e
  . ExceptT String (ReaderT TypeInferenceEnv (StateT TypeInferenceState (Eff (| e)))) a

runTypeInference
  :: forall a e
   . TypeInference a
  -> Eff (| e) (Tuple (Either String a) TypeInferenceState)
runTypeInference t = do
  t' <- runStateT (runReaderT (runExceptT t) initTypeInferenceEnv) initTypeInferenceState
  pure $ t'
  where
    initTypeInferenceEnv = TypeInferenceEnv
    initTypeInferenceState = TypeInferenceState { supply: 0
                                                , subst: Map.empty
                                                }

newTyVar :: String -> TypeInference Type
newTyVar prefix = do
  (TypeInferenceState s) <- get
  _ <- put $ TypeInferenceState s{ supply = s.supply + 1 }
  pure (TVar $ prefix <> show s.supply)

instantiate :: Scheme -> TypeInference Type
instantiate (Scheme vars t) = do
  nvars <- traverse (\_ -> newTyVar "a") vars
  let s = Map.fromFoldable (zip vars nvars)
  pure $ applySubst s t

unifyTypes :: Type -> Type -> TypeInference Subst
unifyTypes t1 t2 = case t1, t2 of
  TFun l r, TFun l' r' -> do
    s1 <- unifyTypes l l'
    s2 <- unifyTypes (applySubst s1 r) (applySubst s1 r')
    pure $ s1 `composeSubst` s2
  TVar u, t            -> varBind u t
  t, TVar u            -> varBind u t
  TNumber, TNumber     -> pure nullSubst
  TBoolean, TBoolean   -> pure nullSubst
  TString, TString     -> pure nullSubst
  _, _                 -> throwError $ "types do not unify: " <> show t1 <> "vs. " <> show t2

varBind :: String -> Type -> TypeInference Subst
varBind u t | t == TVar u = pure nullSubst
            | u `Set.member` getFreeTypeVars t = throwError $ "occur check fails: " <> u <> " vs. " <> show t
            | otherwise = pure $ Map.singleton u t

typeInferLit :: TypeEnv -> Lit -> TypeInference (Tuple Subst Type)
typeInferLit _ l = pure $ Tuple nullSubst $ case l of
  LNumber _  -> TNumber
  LBoolean _ -> TBoolean
  LString _  -> TString

typeInfer :: TypeEnv -> Exp -> TypeInference (Tuple Subst Type)
typeInfer (TypeEnv env) (EVar n) = case Map.lookup n env of
  Nothing    -> throwError $ "unbound variable: " <> n
  Just sigma -> do
    t <- instantiate sigma
    pure $ Tuple nullSubst t

typeInfer env exp                = case exp of
  ELit l       -> typeInferLit env l

  EAbs n e     -> do
    tv <- newTyVar "a"
    let TypeEnv env' = remove env n
        env'' = TypeEnv $ env' `Map.union` Map.singleton n (Scheme [] tv)
    Tuple s1 t1 <- typeInfer env'' e
    pure $ Tuple s1 $ TFun (applySubst s1 tv) t1

  EApp e1 e2   -> do
    tv <- newTyVar "a"
    Tuple s1 t1 <- typeInfer env e1
    Tuple s2 t2 <- typeInfer (applySubst s1 env) e2
    s3 <- unifyTypes (applySubst s2 t1) (TFun t2 tv)
    pure $ Tuple (s3 `composeSubst` s2 `composeSubst` s1) (applySubst s3 tv)

  ELet x e1 e2 -> do
    Tuple s1 t1 <- typeInfer env e1
    let TypeEnv env' = remove env x
        t' = generalize (applySubst s1 env) t1
        env'' = TypeEnv $ Map.insert x t' env'
    Tuple s2 t2 <- typeInfer (applySubst s1 env'') e2
    pure $ Tuple (s1 `composeSubst` s2) t2
  e            -> typeInfer env e

typeInference :: Map.Map String Scheme -> Exp -> TypeInference Type
typeInference env e = do
  Tuple s t <- typeInfer (TypeEnv env) e
  pure $ applySubst s t

instance showType :: Show Type where
  show = case _ of
    TVar n   -> n
    TNumber  -> "Number"
    TBoolean -> "Boolean"
    TString  -> "String"
    TFun t s -> showParenType t <> " -> " <> show s

showParenType :: Type -> String
showParenType t = case t of
  TFun _ _ -> "(" <> show t <> ")"
  _        -> show t

instance showScheme :: Show Scheme where
  show (Scheme vars t) =
    "All "
    <> (show $ ((_ <> ", ") <<< show) <$> vars)
    <> "."
    <> show t
