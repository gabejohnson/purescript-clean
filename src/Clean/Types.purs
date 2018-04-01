module Clean.Types where

import Control.Monad.Eff (Eff)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Data.Array (fromFoldable)
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set as Set
import Prelude (class Eq, class Ord, class Show, map, show, ($), (<$>), (<<<), (<>))

class Types a where
  getFreeTypeVars :: a -> Set.Set String
  applySubst :: Subst -> a -> a

instance typesArray :: Types a => Types (Array a) where
  getFreeTypeVars = Set.unions <<< map getFreeTypeVars
  applySubst = map <<< applySubst

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

-- Type schemes
--   type variables: forall a b
--   type: a -> b -> SomeType)
data Scheme = Scheme (Array String) Type

instance typesScheme :: Types Scheme where
  getFreeTypeVars (Scheme vars t) = getFreeTypeVars t `Set.difference` Set.fromFoldable vars
  applySubst s (Scheme vars t) = Scheme vars $ applySubst (foldr Map.delete s vars) t

-- Type substitutions
type Subst = Map.Map String Type

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

instance typesTypeEnv :: Types TypeEnv where
  getFreeTypeVars (TypeEnv env) = getFreeTypeVars $ fromFoldable (Map.values env)
  applySubst s (TypeEnv env) = TypeEnv $ map (applySubst s) env

type TypeInference a
  = forall e
  . ExceptT String (ReaderT TypeInferenceEnv (StateT TypeInferenceState (Eff (| e)))) a

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

data TypeInferenceEnv = TypeInferenceEnv
data TypeInferenceState = TypeInferenceState { supply :: Int
                                             , subst :: Subst
                                             }
