module Clean.Expressions (Exp(..), Lit(..), babylonToClean) where

import Babylon.Types (BinaryExpression', BinaryOperator(..), Node(..), VariableKind(Let))
import Control.Monad.Except (Except, throwError)
import Data.Array (length, unsnoc)
import Data.Foldable (foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence, traverse)
import Prelude (class Eq, class Ord, class Show, bind, join, pure, show, ($), (<$>), (<*>), (<>))

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
babylonToClean = case _ of
  Identifier              e -> identifierToEVar e
  NumericLiteral          e -> literalToELit LNumber e
  BooleanLiteral          e -> literalToELit LBoolean e
  StringLiteral           e -> literalToELit LString e
  CallExpression          e -> callToEApp e
  ArrowFunctionExpression e -> arrowToEAbs e
  BinaryExpression        e -> binaryExpressionToEApp e
  n                         -> throwError $ "Unsupported expression type " <> show n

binaryExpressionToEApp :: BinaryExpression' ( operator :: BinaryOperator ) -> Expression
binaryExpressionToEApp { left, right, operator } = do
  left' <- babylonToClean left
  right' <- babylonToClean right
  (\op -> EApp (EApp op left') right') <$> binopToEVar operator
    where
      unsupportedMessage = "Unsupported binary operator " <> show operator
      binopToEVar op = case op of
        Equals       -> throwError unsupportedMessage
        NotEquals    -> throwError unsupportedMessage
        In           -> throwError unsupportedMessage
        Instanceof   -> throwError unsupportedMessage
        Pipe         -> throwError unsupportedMessage
        Identical    -> pure $ EVar "(==)"
        NotIdentical -> pure $ EVar "(!=)"
        _            -> pure $ EVar $ "(" <> show op <> ")"

identifierToEVar :: forall r. { name :: String | r }-> Expression
identifierToEVar { name } = pure $ EVar name

literalToELit :: forall a r. (a -> Lit) -> { value :: a | r } -> Expression
literalToELit ctor { value } = pure $ ELit $ ctor value

callToEApp :: forall r. { arguments :: Array Node, callee :: Node | r } -> Expression
callToEApp { arguments, callee } = case arguments of
  [arg] -> do
    let arg'    = babylonToClean arg
    let callee' = babylonToClean callee
    EApp <$> callee' <*> arg'
  _     -> throwError $
           "Wrong number of arguments ("
           <> show (length arguments) <> ") in "
           <> show arguments

arrowToEAbs :: forall r. { params :: Array Node, body :: Node | r } -> Expression
arrowToEAbs { params, body } = case params of
  [Identifier { name }] -> EAbs name <$> functionBodyToExp body
  _ -> throwError $
       "Wrong number of parameters ("
       <> show (length params) <> ") in "
       <> show params

functionBodyToExp :: Node -> Expression
functionBodyToExp = case _ of
  BlockStatement body -> blockStatementToELet body
  n                   -> babylonToClean n
    where
      blockStatementToELet { body } = case unsnoc body of
        Just { init: decls
             , last: (ReturnStatement { argument })
             }  -> bodyToELet decls argument
        Nothing -> throwError $ "Empty block statements not allowed."
        _       -> throwError $ "Improper block statement " <> show body

bodyToELet :: Array Node -> Maybe Node -> Expression
bodyToELet decls ret = do
  decls' <- variableDeclarationsToDeclarators decls
  foldr reducer (returnToELet ret) decls' where
    returnToELet = case _ of
      Just arg -> babylonToClean arg
      Nothing  -> throwError "Functions must return values."

    reducer { id, init } acc = case init of
      Nothing    -> throwError "`let` declarations must be initialized"
      Just init' -> ELet id <$> babylonToClean init' <*> acc

    variableDeclarationsToDeclarators ns = join <$> (traverse go ns) where
      fromDeclarator = case _ of
        VariableDeclarator { id: (Identifier { name })
                           , init
                           } -> pure { id: name, init }
        _                    -> throwError $ "Impossible state!"

      go = case _ of
        VariableDeclaration { kind: Let
                            , declarations
                            }        -> sequence $ fromDeclarator <$> declarations
        VariableDeclaration { kind } -> throwError $
                                        "Invalid declaration type "
                                        <> show kind
                                        <> ". Only `let` declarations are allowed"

        d                            -> throwError $
                                        "Invalid statement "
                                        <> show d
                                        <> ". Only `let` and `return` statements are allowed."
