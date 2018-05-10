module Clean
  ( defaultEnv
  , runTypeInference
  , typeInference
  ) where

import Prelude

import Clean.Types (Constraint, Exp(..), Kind(..), Label, Prim(..), Scheme(..), Subst, TyVar(..), Type(..), TypeEnv(..), TypeInference, TypeInferenceEnv(..), TypeInferenceState(..), applySubst, getFreeTypeVars, toList)
import Control.Monad.Eff (Eff)
import Control.Monad.Except.Trans (runExceptT, throwError)
import Control.Monad.Reader.Trans (runReaderT)
import Control.Monad.State.Trans (get, put, runStateT)
import Data.Array as A
import Data.Either (Either)
import Data.Foldable (class Foldable, foldM)
import Data.List as L
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Set as S
import Data.String as Str
import Data.Traversable (traverse)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))

nullSubst :: Subst
nullSubst = M.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = map (applySubst s1) s2 `M.union` s1

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (M.delete var env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = S.toUnfoldable $ getFreeTypeVars t `S.difference` getFreeTypeVars env

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
                                                , subst: M.empty
                                                }

freshTyVar :: TypeInference Type
freshTyVar = newTyVar "t"

newTyVar :: String -> TypeInference Type
newTyVar = newTyVarWith TypeKind S.empty

newTyVarWith :: Kind -> Constraint -> Label -> TypeInference Type
newTyVarWith kind constraint prefix = do
  TypeInferenceState s <- get
  _ <- put $ TypeInferenceState s { supply = s.supply + 1 }
  let name = prefix <> show s.supply
  pure $ TVar $ TyVar { name, kind, constraint }

instantiate :: Scheme -> TypeInference Type
instantiate (Scheme vars t) = do
  nvars <- traverse newVar vars
  let s = M.fromFoldable (L.zip vars nvars)
  pure $ applySubst s t
  where
    newVar :: TyVar -> TypeInference Type
    newVar (TyVar {name, kind, constraint}) | chars <- Str.toCharArray name =
      newTyVarWith kind constraint case A.uncons chars of
        Nothing -> "a"
        Just { head, tail } -> Str.singleton head

unifyTypes :: Type -> Type -> TypeInference Subst
unifyTypes t1 t2 = case t1, t2 of
  TFun l1 r1, TFun l2 r2  -> do
    s1 <- unifyTypes l1 l2
    s2 <- unifyTypes (applySubst s1 r1) (applySubst s1 r2)
    pure $ s1 `composeSubst` s2
  TVar u, TVar v          -> unionConstraints u v
  TVar u, _               -> varBind u t2
  _, TVar u               -> varBind u t1
  TNumber, TNumber        -> pure nullSubst
  TBoolean, TBoolean      -> pure nullSubst
  TString, TString        -> pure nullSubst
  TArray u, TArray v      -> unifyTypes u v
  TRecord r1, TRecord r2  -> unifyTypes r1 r2
  TRowEmpty, TRowEmpty    -> pure nullSubst

  TRowExtend label1 fieldType1 rowTail1
  , row2@(TRowExtend _ _ _) -> do

    { fieldType: fieldType2
    , rowTail:   rowTail2
    , subst:     subst1
    }                    <- rewriteRow label1 row2

    case (toList rowTail1).tyVar of
      -- ensure termination
      Just tv | M.member tv subst1 -> throwError "recursive row type"
      _                        -> do
        subst2 <- unifyTypes (applySubst subst1 fieldType1) (applySubst subst1 fieldType2)

        let subst3 = subst2 `composeSubst` subst1

        subst4 <- unifyTypes (applySubst subst3 rowTail1) (applySubst subst3 rowTail2)

        pure $ subst4 `composeSubst` subst3
  _, _                      -> throwError $ "types do not unify: " <> show t1 <> " vs. " <> show t2


-- union lacks constraints when unifying row type variables
unionConstraints :: TyVar -> TyVar -> TypeInference Subst
unionConstraints u@(TyVar u') v@(TyVar v')
  | u == v    = pure nullSubst
  | otherwise =
    case u'.kind, v'.kind of
      TypeKind, TypeKind -> pure $ M.singleton u (TVar v)
      RowKind, RowKind   -> do
        let c = u'.constraint `S.union` v'.constraint
        r <- newTyVarWith RowKind c "r"
        pure $ M.fromFoldable [u /\ r, v /\ r]
      _, _               -> throwError "kind mismatch"

rewriteRow :: Label -> Type -> TypeInference { fieldType :: Type, rowTail :: Type, subst :: Subst }
rewriteRow newLabel = case _ of
  TRowEmpty                 -> throwError $ "label " <> newLabel <> " cannot be inserted"
  (TRowExtend label fieldType rowTail)
    | newLabel == label     -> pure { fieldType, rowTail, subst: nullSubst } -- nothing to do

    | TVar rt <- rowTail    -> do
      r <- newTyVarWith RowKind (lacks newLabel) "r"
      a <- freshTyVar
      subst <- varBindRow rt $ TRowExtend newLabel a r

      pure { fieldType: a
           , rowTail: applySubst subst $ TRowExtend label fieldType r
           , subst
           }


    | otherwise             -> do
      row <- rewriteRow newLabel rowTail

      pure $ row { rowTail = TRowExtend label fieldType row.rowTail }

  t                         -> throwError $ "Unexpected type: " <> show t

varBind :: TyVar -> Type -> TypeInference Subst
varBind u@(TyVar u') t | t == TVar u = pure nullSubst
            | u `S.member` getFreeTypeVars t = throwError $ "occur check fails: "
                                                 <> show u
                                                 <> " vs. "
                                                 <> show t
            | otherwise =
              case u'.kind of
                TypeKind -> pure $ M.singleton u t
                RowKind  -> varBindRow u t

varBindRow :: TyVar -> Type -> TypeInference Subst
varBindRow u@(TyVar u') t = case L.fromFoldable (ls `S.intersection` ls') of
  L.Nil | Nothing <- tyVar -> pure s1
        | Just r1@(TyVar {constraint}) <- tyVar -> do
          let c = ls `S.union` constraint
          r2 <- newTyVarWith RowKind c "r"
          let s2 = M.singleton r1 r2
          pure $ s1 `composeSubst` s2
  labels                          -> throwError $ "repeated label(s): " <> show labels
  where
    ls              = u'.constraint
    { rows, tyVar } = toList t
    ls'             = S.fromFoldable $ _.label <$> rows
    s1              = M.singleton u t

typeInfer :: TypeEnv -> Exp -> TypeInference { subst :: Subst, type :: Type }
typeInfer env@(TypeEnv te) = case _ of
  EVar n       -> case M.lookup n te of
    Nothing    -> throwError $ "unbound variable: `" <> n <> "`"
    Just scheme -> {subst: nullSubst, type: _} <$> instantiate scheme

  EPrim p       ->  {subst: nullSubst, type: _} <$> typeInferPrim env p
  EAbs n e     -> do
    tv <- freshTyVar
    let TypeEnv env2 = remove env n
        env3 = TypeEnv $ env2 `M.union` M.singleton n (Scheme mempty tv)
    {subst: s1, type: t1 } <- typeInfer env3 e
    pure $ {subst: s1, type: TFun (applySubst s1 tv) t1}

  EApp e1 e2   -> do
    {subst: s1, type: t1} <- typeInfer env e1
    {subst: s2, type: t2} <- typeInfer (applySubst s1 env) e2
    tv <- freshTyVar
    s3 <- unifyTypes (applySubst s2 t1) (TFun t2 tv)
    pure $ {subst: s3 `composeSubst` s2 `composeSubst` s1, type: applySubst s3 tv}

  ELet x e1 e2 -> do
    {subst: s1, type: t1} <- typeInfer env e1
    let TypeEnv env2 = remove env x
        scheme = generalize (applySubst s1 env) t1
        env3 = TypeEnv $ M.insert x scheme env2
        env4 = applySubst s1 env3
    {subst: s2, type: t2} <- typeInfer env4 e2
    pure $ {subst: s1 `composeSubst` s2, type: t2}

typeInferPrim :: TypeEnv -> Prim -> TypeInference Type
typeInferPrim env = case _ of
    LNumber _        -> pure TNumber
    LBoolean _       -> pure TBoolean
    LString _        -> pure TString

    LArray xs        -> do
      emptyType <- freshTyVar
      TArray <$> inferExpressionSequence env emptyType xs

    Cond             -> do
      a <- freshTyVar
      pure $ TFun TBoolean (TFun a (TFun a a))

    RecordEmpty      -> pure $ TRecord TRowEmpty

    RecordSelect l   -> do
      a <- freshTyVar
      r <- newTyVarWith RowKind (lacks l) "r"
      pure $ TFun (TRecord $ TRowExtend l a r) a

    RecordExtend l   -> do
      a <- freshTyVar
      r <- newTyVarWith RowKind (lacks l) "r"
      pure $ TFun a (TFun (TRecord r) (TRecord $ TRowExtend l a r))

    RecordRestrict l -> do
      a <- freshTyVar
      r <- newTyVarWith RowKind (lacks l) "r"
      pure $ TFun (TRecord $ TRowExtend l a r) (TRecord r)
    where
      inferExpressionSequence :: forall f m. Foldable f => TypeEnv -> Type -> f Exp -> TypeInference Type
      inferExpressionSequence env emptyType ts = foldM (\t1 expr -> do
          { type: t2 } <- typeInfer env expr
          _ <- unifyTypes t1 t2
          pure t2)
        emptyType ts


typeInference :: Exp -> TypeInference Type
typeInference e = do
  TypeInferenceState s <- get
  {subst, type: t} <- typeInfer s.env e
  pure $ applySubst subst t

lacks :: Label -> Constraint
lacks = S.singleton

mkTyVar :: String -> TyVar
mkTyVar name = TyVar { name, kind: TypeKind, constraint: S.empty }

defaultEnv :: TypeEnv
defaultEnv = TypeEnv $ M.fromFoldable
             [ "minus"  /\ (Scheme mempty $ TFun TNumber TNumber)
             , "negate" /\ (Scheme mempty $ TFun TNumber TNumber)
             , "(~)"    /\ (Scheme mempty $ TFun TNumber TNumber)
             , "(!)"    /\ (Scheme mempty $ TFun TBoolean TBoolean)
             , "typeof" /\ (Scheme mempty $ TFun (TVar $ mkTyVar "a") TString)
             , "(+)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(-)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(*)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(/)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(%)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(**)"   /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(<<)"   /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(>>)"   /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(>>>)"  /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(|)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(^)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(&)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TNumber))
             , "(<)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TBoolean))
             , "(<=)"   /\ (Scheme mempty $ TFun TNumber (TFun TNumber TBoolean))
             , "(>=)"   /\ (Scheme mempty $ TFun TNumber (TFun TNumber TBoolean))
             , "(>)"    /\ (Scheme mempty $ TFun TNumber (TFun TNumber TBoolean))
             , "(===)"  /\ (Scheme (pure $ mkTyVar "a") $
                            TFun (TVar $ mkTyVar "a") (TFun (TVar $ mkTyVar "a") TBoolean))
             , "(!==)"  /\ (Scheme (pure $ mkTyVar "a") $
                            TFun (TVar $ mkTyVar "a") (TFun (TVar $ mkTyVar "a") TBoolean))
             ]
