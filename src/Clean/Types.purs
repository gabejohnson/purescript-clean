module Clean.Types where

import Control.Monad.Eff (Eff)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Data.Array (fromFoldable)
import Data.Foldable (foldr)
import Data.List (List(..), (:))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set as Set
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Partial.Unsafe (unsafePartial)
import Prelude (class Eq, class Ord, class Show, map, show, ($), (<$>), (<<<), (<>))

class Types a where
  getFreeTypeVars :: a -> Set.Set String
  applySubst :: Subst -> a -> a

instance typesArray :: Types a => Types (Array a) where
  getFreeTypeVars = Set.unions <<< map getFreeTypeVars
  applySubst = map <<< applySubst

-- Types
data Type
  = TVar String
  | TNumber
  | TBoolean
  | TString
  | TFun Type Type
  | TRecord Type
  | TRowEmpty
  | TRowExtend String Type Type
derive instance eqType :: Eq Type
derive instance ordType :: Ord Type

instance typesType :: Types Type where
  getFreeTypeVars = case _ of
    TVar n           -> Set.singleton n
    TFun t1 t2       -> getFreeTypeVars t1 `Set.union` getFreeTypeVars t2
    TRecord t        -> getFreeTypeVars t
    TRowExtend l t r -> getFreeTypeVars r `Set.union` getFreeTypeVars t
    _                -> Set.empty

  applySubst s = case _ of
    TVar n     -> fromMaybe (TVar n) $ Map.lookup n s
    TFun t1 t2 -> TFun (applySubst s t1) (applySubst s t2)
    TRecord t  -> TRecord (applySubst s t)
    TRowExtend l t r -> TRowExtend l (applySubst s t) (applySubst s r)
    t          -> t

-- Type schemes
--   type variables: forall a b
--   type: a -> b -> SomeType
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
  show = unsafePartial case _ of
    TVar n    -> n
    TNumber   -> "Number"
    TBoolean  -> "Boolean"
    TString   -> "String"
    TFun t s  -> showParenType t <> " -> " <> show s
    TRecord r -> "{ " <> showRow r <> " }"
      where
        showRow r = (foldr (\e s -> s <> showEntry e) "" ls) <> maybe "" (showRowTail ls) mv
          where
            ls /\ mv = toList r
        showEntry (l /\ t) = l <> ": " <> show t <> ", "
        showRowTail = case _, _ of
          Nil, r -> show r
          _  , r -> " | " <> show r

showParenType :: Type -> String
showParenType t = case t of
  TFun _ _ -> "(" <> show t <> ")"
  _        -> show t

instance showScheme :: Show Scheme where
  show (Scheme vars t) =
    "forall "
    <> (show $ ((_ <> ", ") <<< show) <$> vars)
    <> "."
    <> show t

data TypeInferenceEnv = TypeInferenceEnv
data TypeInferenceState = TypeInferenceState { supply :: Int
                                             , subst :: Subst
                                             }

toList :: Type -> Tuple (List (Tuple String Type)) (Maybe String)
toList = unsafePartial $ case _ of
  TVar r -> Nil /\ Just r
  TRowEmpty -> Nil /\ Nothing
  TRowExtend l t r -> let ls /\ mv = toList r
                      in ((l /\ t) : ls) /\ mv
