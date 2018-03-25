module Clean.Expressions (Exp(..), Lit(..), babylonToClean) where

import Babylon.Types (Node(..))
import Control.Monad.Except (Except, throwError)
import Data.Array (length)
import Data.Array.Partial (head)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafePartial)
import Prelude (class Eq, class Ord, class Show, bind, otherwise, pure, show, ($), (<$>), (<*>), (<>), (==))

-- Expressions
data Exp = EVar String
         | ELit Lit
         | EApp Exp Exp
         | EAbs String Exp
         | ELet String Exp Exp
derive instance eqExp :: Eq Exp
derive instance ordExp :: Ord Exp

instance showExp :: Show Exp where
  show = case _ of
    EVar name     -> name
    ELit lit      -> show lit
    ELet x b body -> "let " <> x <> " = " <> show b <> " in " <> show body
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

-- Literals
data Lit = LNumber Number
         | LBoolean Boolean
         | LString String
derive instance eqLit :: Eq Lit
derive instance ordLit :: Ord Lit

instance showLit :: Show Lit where
  show = case _ of
    LNumber  n -> show n
    LBoolean b -> if b then "true" else "false"
    LString  s -> "\"" <> s <> "\""

type Expression = Except String Exp

babylonToClean :: Node -> Expression
babylonToClean n = case n of
  Identifier              _ -> identifierToEVar n
  NumericLiteral          _ -> literalToELit n
  BooleanLiteral          _ -> literalToELit n
  StringLiteral           _ -> literalToELit n
  CallExpression          _ -> callToEApp n
  ArrowFunctionExpression _ -> arrowToEAbs n
  VariableDeclaration     _ -> variableDeclarationToELet n
  _                         -> throwError $ "Unsupported expression type " <> show n

identifierToEVar :: Node -> Expression
identifierToEVar = case _ of
  Identifier { loc, name } -> pure $ EVar name
  n                        -> throwError $ "Not an identifier " <> show n

literalToELit :: Node -> Expression
literalToELit =
  case _ of
    NumericLiteral l -> pure $ ELit $ LNumber l.value
    BooleanLiteral l -> pure $ ELit $ LBoolean l.value
    StringLiteral  l -> pure $ ELit $ LString l.value
    n                -> throwError $ "Unsupported literal " <> show n

callToEApp :: Node -> Expression
callToEApp = case _ of
  CallExpression c@{ arguments, callee }
    | length arguments == 1 -> do
      let arg = unsafePartial head arguments
      let arg' = babylonToClean arg
      let callee' = babylonToClean callee
      EApp <$> callee' <*> arg'
    | otherwise             -> throwError $ "Too many arguments " <> show arguments
  n                         -> throwError $ "Not a call expression " <> show n

arrowToEAbs :: Node -> Expression
arrowToEAbs = case _ of
  ArrowFunctionExpression f@{ params, body }
    | length params == 1 -> do
      let param = unsafePartial head params
      EAbs <$> getIdentifierName param <*> babylonToClean body
    | otherwise             -> throwError $ "Too many parameters " <> show params
  n                         -> throwError $ "Unsupported function type " <> show n

getIdentifierName :: Node -> Except String String
getIdentifierName = case _ of
  Identifier {name} -> pure name
  n            -> throwError $ "Not an identifier " <> show n

variableDeclarationToELet :: Node -> Expression
-- TODO: Need to deal w/ different kinds of variables (let, var, const)
variableDeclarationToELet n = case n of
  VariableDeclaration d@{ declarations, kind }
    | length declarations == 1 -> do
      let decl = unsafePartial $ head declarations
      getDeclarator decl
    | otherwise                -> throwError $ "Too many declarators " <> show n
  _                            -> throwError $ "Not a variable" <> show n

getDeclarator :: Node -> Expression
getDeclarator n = case n of
  VariableDeclarator d@{ id: id', init } -> do
    id'' <-  getIdentifierName id'
    case init of
      Just i -> (ELet id'') <$> (babylonToClean i) <*> pure (EVar id'')
      Nothing -> throwError $ "Missing declaration initializer " <> show n
  _ -> throwError $ "Not a variable declarator " <> show n
