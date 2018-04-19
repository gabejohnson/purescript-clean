module Clean
  ( defaultEnv
  , runTypeInference
  , typeInference
  ) where

import Prelude

import Clean.Expressions (Exp(..), Prim(..))
import Clean.Types (Scheme(..), Subst, Type(..), TypeEnv(..), TypeInference, TypeInferenceEnv(..), TypeInferenceState(..), applySubst, getFreeTypeVars, toList)
import Control.Monad.Eff (Eff)
import Control.Monad.Except.Trans (runExceptT, throwError)
import Control.Monad.Reader.Trans (runReaderT)
import Control.Monad.State.Trans (get, put, runStateT)
import Data.Array (zip)
import Data.Either (Either)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested ((/\))

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = map (applySubst s1) s2 `Map.union` s1

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toUnfoldable $ getFreeTypeVars t `Set.difference` getFreeTypeVars env

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
  TRecord r1, TRecord r2 -> unifyTypes r1 r2
  TRowEmpty, TRowEmpty -> pure nullSubst
  TRowExtend l1 f1 rt1
  , r2@(TRowExtend _ _ _) -> do
    { field, rowTail, theta } <- rewriteRow l1 r2
    case snd $ toList rt1 of
      Just tv | Map.member tv theta -> throwError "recursive row type"
      _                           -> do
        theta2 <- unifyTypes (applySubst theta f1) (applySubst theta field)
        let s = theta2 `composeSubst` theta
        theta3 <- unifyTypes (applySubst s rt1) (applySubst s rowTail)
        pure $ theta3 `composeSubst` s
  _, _                 -> throwError $ "types do not unify: " <> show t1 <> " vs. " <> show t2

rewriteRow :: String -> Type -> TypeInference { field :: Type, rowTail :: Type, theta :: Subst }
rewriteRow newLabel = case _ of
  TRowEmpty                 -> throwError $ "label " <> newLabel <> " cannot be inserted"
  (TRowExtend label field rowTail)
    | newLabel == label     -> pure { field, rowTail, theta: nullSubst } -- nothing to do
    | TVar alpha <- rowTail -> do
      beta <- newTyVar "r"
      gamma <- newTyVar "a"
      pure { field: gamma
           , rowTail: TRowExtend label field beta
           , theta: Map.singleton alpha $ TRowExtend newLabel gamma beta
           }
    | otherwise             -> do
      row <- rewriteRow newLabel rowTail
      pure $ row { rowTail = TRowExtend label row.field rowTail }
  t                         -> throwError $ "Unexpected type: " <> show t

varBind :: String -> Type -> TypeInference Subst
varBind u t | t == TVar u = pure nullSubst
            | u `Set.member` getFreeTypeVars t = throwError $ "occur check fails: " <> u <> " vs. " <> show t
            | otherwise = pure $ Map.singleton u t

typeInfer :: TypeEnv -> Exp -> TypeInference (Tuple Subst Type)
typeInfer env@(TypeEnv te) = case _ of
  EVar n       -> case Map.lookup n te of
    Nothing    -> throwError $ "unbound variable: `" <> n <> "`"
    Just sigma -> (nullSubst /\ _) <$> instantiate sigma

  EPrim p       ->  (Tuple nullSubst) <$> typeInferPrim p
  EAbs n e     -> do
    tv <- newTyVar "a"
    let TypeEnv env' = remove env n
        env'' = TypeEnv $ env' `Map.union` Map.singleton n (Scheme [] tv)
    s1 /\ t1 <- typeInfer env'' e
    pure $ s1 /\ TFun (applySubst s1 tv) t1

  EApp e1 e2   -> do
    tv <- newTyVar "a"
    s1 /\ t1 <- typeInfer env e1
    s2 /\ t2 <- typeInfer (applySubst s1 env) e2
    s3 <- unifyTypes (applySubst s2 t1) (TFun t2 tv)
    pure $ s3 `composeSubst` s2 `composeSubst` s1 /\ applySubst s3 tv

  ELet x e1 e2 -> do
    s1 /\ t1 <- typeInfer env e1
    let TypeEnv env' = remove env x
        t' = generalize (applySubst s1 env) t1
        env'' = TypeEnv $ Map.insert x t' env'
    s2 /\ t2 <- typeInfer (applySubst s1 env'') e2
    pure $ s1 `composeSubst` s2 /\ t2

typeInferPrim :: Prim -> TypeInference Type
typeInferPrim = case _ of
    LNumber _        -> pure TNumber
    LBoolean _       -> pure TBoolean
    LString _        -> pure TString

    Cond             -> do
      a <- newTyVar "a"
      pure $ TFun TBoolean (TFun a (TFun a a))

    RecordEmpty      -> pure $ TRecord TRowEmpty

    RecordSelect l   -> do
      a <- newTyVar "a"
      r <- newTyVar "r"
      pure $ TFun (TRecord $ TRowExtend l a r) a

    RecordExtend l   -> do
      a <- newTyVar "a"
      r <- newTyVar "r"
      pure $ TFun a (TFun (TRecord r) (TRecord $ TRowExtend l a r))

    RecordRestrict l -> do
      a <- newTyVar "a"
      r <- newTyVar "r"
      pure $ TFun (TRecord $ TRowExtend l a r) (TRecord r)

typeInference :: Map.Map String Scheme -> Exp -> TypeInference Type
typeInference env e = do
  s /\ t <- typeInfer (TypeEnv env) e
  pure $ applySubst s t

defaultEnv :: Map.Map String Scheme
defaultEnv =
  Map.fromFoldable [ "minus"  /\ (Scheme [] $ TFun TNumber TNumber)
                   , "negate" /\ (Scheme [] $ TFun TNumber TNumber)
                   , "(~)"    /\ (Scheme [] $ TFun TNumber TNumber)
                   , "(!)"    /\ (Scheme [] $ TFun TBoolean TBoolean)
                   , "typeof" /\ (Scheme [] $ TFun (TVar "a") TString)
                   , "(+)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(-)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(*)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(/)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(%)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(**)"   /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(<<)"   /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(>>)"   /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(>>>)"  /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(|)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(^)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(&)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TNumber))
                   , "(<)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TBoolean))
                   , "(<=)"   /\ (Scheme [] $ TFun TNumber (TFun TNumber TBoolean))
                   , "(>=)"   /\ (Scheme [] $ TFun TNumber (TFun TNumber TBoolean))
                   , "(>)"    /\ (Scheme [] $ TFun TNumber (TFun TNumber TBoolean))
                   , "(===)"  /\ (Scheme ["a"] $ TFun (TVar "a") (TFun (TVar "a") TBoolean))
                   , "(!==)"  /\ (Scheme ["a"] $ TFun (TVar "a") (TFun (TVar "a") TBoolean))
                   ]
