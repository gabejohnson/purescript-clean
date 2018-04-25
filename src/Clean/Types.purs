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
import Partial.Unsafe (unsafePartial)
import Prelude (class Eq, class Ord, class Show, map, show, ($), (<$>), (<<<), (<>))

type Label = String
type Name = String

-- Expressions
data Exp
  = EVar Name
  | EPrim Prim
  | EApp Exp Exp
  | EAbs Name Exp
  | ELet Name Exp Exp
derive instance eqExp :: Eq Exp
derive instance ordExp :: Ord Exp

instance showExp :: Show Exp where
  show = case _ of
    EVar n        -> n
    EPrim p       -> show p
    ELet n b body -> "let " <> n <> " = " <> show b <> " in " <> show body
    EApp e1 e2    -> show e1 <> " " <> showParenExp e2
    EAbs n e      -> "\\" <> n <> " -> " <> show e

showParenExp :: Exp -> String
showParenExp t = case t of
  ELet _ _ _ -> parenWrap $ show t
  EApp _ _   -> parenWrap $ show t
  EAbs _ _   -> parenWrap $ show t
  _          -> show t

parenWrap :: String -> String
parenWrap s = "(" <> s <> ")"

-- Primitives
data Prim
  = LNumber Number
  | LBoolean Boolean
  | LString String
  | Cond
  | RecordEmpty
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
derive instance eqPrim :: Eq Prim
derive instance ordPrim :: Ord Prim

instance showPrim :: Show Prim where
  show = case _ of
    LNumber  n       -> show n
    LBoolean b       -> if b then "true" else "false"
    LString  s       -> "\"" <> s <> "\""
    Cond             -> "(_?_:_)"
    RecordSelect l   -> "(_." <> l <> ")"
    RecordExtend l   -> "{" <> l <> ":_|_}"
    RecordRestrict l -> "(_-" <> l <> ")"
    RecordEmpty      -> "{}"

-- Types
data Type
  = TVar TyVar
  | TNumber
  | TBoolean
  | TString
  | TFun Type Type
  | TRecord Type
  | TRowEmpty
  | TRowExtend Label Type Type
derive instance eqType :: Eq Type
derive instance ordType :: Ord Type

data TyVar = TyVar
  { name :: Name
  , kind :: Kind
  , constraint :: Constraint
  }
derive instance eqTyVar :: Eq TyVar
derive instance ordTyVar :: Ord TyVar
instance showTyVar :: Show TyVar where
  show (TyVar { name }) = name
-- row type variables may have constraints
data Kind = TypeKind | RowKind
derive instance eqKind :: Eq Kind
derive instance ordKind :: Ord Kind

-- labels the associated tyvar must lack, for types of kind row
type Constraint = Set.Set Label

-- Type schemes
--   type variables: forall a b
--   type: a -> b -> SomeType
data Scheme = Scheme (List TyVar) Type

class Types a where
  getFreeTypeVars :: a -> Set.Set TyVar
  applySubst :: Subst -> a -> a

instance typesArray :: Types a => Types (Array a) where
  getFreeTypeVars = Set.unions <<< map getFreeTypeVars
  applySubst = map <<< applySubst

instance typesType :: Types Type where
  getFreeTypeVars = case _ of
    TVar t           -> Set.singleton t
    TFun t1 t2       -> getFreeTypeVars t1 `Set.union` getFreeTypeVars t2
    TRecord r        -> getFreeTypeVars r
    TRowExtend l t r -> getFreeTypeVars r `Set.union` getFreeTypeVars t
    _                -> Set.empty

  applySubst s = case _ of
    TVar n           -> fromMaybe (TVar n) $ Map.lookup n s
    TFun t1 t2       -> TFun (applySubst s t1) (applySubst s t2)
    TRecord t        -> TRecord (applySubst s t)
    TRowExtend l t r -> TRowExtend l (applySubst s t) (applySubst s r)
    t                -> t

instance typesScheme :: Types Scheme where
  getFreeTypeVars (Scheme vars t) = getFreeTypeVars t `Set.difference` Set.fromFoldable vars
  applySubst s (Scheme vars t) = Scheme vars $ applySubst (foldr Map.delete s vars) t

-- Type substitutions
type Subst = Map.Map TyVar Type

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

instance typesTypeEnv :: Types TypeEnv where
  getFreeTypeVars (TypeEnv env) = getFreeTypeVars $ fromFoldable (Map.values env)
  applySubst s (TypeEnv env) = TypeEnv $ map (applySubst s) env

type TypeInference a
  = forall e
  . ExceptT String (ReaderT TypeInferenceEnv (StateT TypeInferenceState (Eff (| e)))) a

instance showType :: Show Type where
  show = unsafePartial case _ of
    TVar t    -> show t
    TNumber   -> "Number"
    TBoolean  -> "Boolean"
    TString   -> "String"
    TFun t s  -> showParenType t <> " -> " <> show s
    TRecord r -> "{ " <> showRow r <> " }"
      where
        showRow r = (foldr (\e s -> s <> showEntry e) "" rows) <> maybe "" (showRowTail rows) tyVar
          where
            { rows, tyVar } = toList r
        showEntry { label: l, type: t } = l <> ": " <> show t <> ", "
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

toList :: Type -> { rows :: List { label :: Label, type :: Type }, tyVar :: Maybe TyVar }
toList = unsafePartial $ case _ of
  TVar r           -> { rows: Nil, tyVar: Just r }
  TRowEmpty        -> { rows: Nil, tyVar: Nothing }
  TRowExtend l t r -> let {rows, tyVar} = toList r
                      in { rows: ({label: l, type: t} : rows), tyVar }
