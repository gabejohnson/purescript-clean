module Clean.Expressions (babylonToClean) where

import Babylon.Types (BinaryExpression', BinaryOperator(..), Node(..), Node', ObjectProperty', UnaryOperator(..), VariableKind(Let))
import Clean.Types (Exp(..), Prim(..))
import Control.Monad.Except (Except, throwError)
import Data.Array (last, length, unsnoc)
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Prelude (bind, join, otherwise, pure, show, ($), (<$>), (<*>), (<<<), (<>), (==))


type Expression = Except String Exp

babylonToClean :: Node -> Expression
babylonToClean = case _ of
  File                    f -> fileToExp f
  NumericLiteral          e -> literalToEPrim LNumber e
  BooleanLiteral          e -> literalToEPrim LBoolean e
  StringLiteral           e -> literalToEPrim LString e
  Identifier              e -> identifierToEVar e
  UnaryExpression         e -> unaryExpressionToEApp e
  BinaryExpression        e -> binaryExpressionToEApp e
  ConditionalExpression   e -> conditionalToEApp e
  ArrowFunctionExpression e -> arrowToEAbs e
  CallExpression          e -> callToEApp e
  ObjectExpression        e -> objectToRecord e
  MemberExpression        e -> memberExpressionToEPrim e
  ArrayExpression         e -> arrayExpressionToEPrim e
  -- VariableDeclaration     e -> variableDeclarationToELet e
  n                         -> throwError $ "Unsupported expression type " <> show n

arrayExpressionToEPrim :: forall r. Node' ( elements :: Array (Maybe Node) | r) -> Expression
arrayExpressionToEPrim { elements } = (EPrim <<< LArray) <$> traverse (maybe (throwError $ "Sparse arrays a not supported: " <> show elements) babylonToClean) elements

memberExpressionToEPrim :: forall r. Node' ( object :: Node, property :: Node | r) -> Expression
memberExpressionToEPrim { object, property } = do
  r <- babylonToClean object
  prop <- babylonToClean property
  maybe (throwError $ "Unsupported label type: " <> show prop)
        (\l -> pure $ EApp (EPrim (RecordSelect l)) r)
        $ propertyToString prop

objectToRecord :: Node' (properties :: Array Node) -> Expression
objectToRecord { properties } = foldl go (pure $ EPrim RecordEmpty) properties
  where
    go expr n = case n of
      ObjectProperty { key, value } -> do
        k <- babylonToClean key
        v <- babylonToClean value
        expr' <- expr
        maybe (throwError $ "Unsupported label type: " <> show expr')
              (\l -> pure $ EApp (EApp (EPrim $ RecordExtend l) v) expr')
          $ propertyToString k
      _ -> throwError $ "Unsupported label type: " <> show n

propertyToString :: Exp -> Maybe String
propertyToString = case _ of
  EPrim (LString s) -> Just s
  EVar s            -> Just s
  _                 -> Nothing

fileToExp :: Node' ( program :: Node ) -> Expression
fileToExp { program } = case program of
  Program { body } -> programBodyToELet body
  _                -> throwError "Files must contain programs"

unaryExpressionToEApp ::
  Node' ( operator :: UnaryOperator
        , argument :: Node
        , prefix :: Boolean
        ) -> Expression
unaryExpressionToEApp { operator, argument, prefix } =
  EApp <$> identifier <*> babylonToClean argument
  where
    identifier = EVar <$> case operator of
      Throw  -> throwError $ "Unsupported unary operator " <> show operator
      Delete -> throwError $ "Unsupported unary operator " <> show operator
      Void   -> throwError $ "Unsupported unary operator " <> show operator
      Minus  -> pure $ "minus"
      Plus   -> pure $ "plus"
      Typeof -> pure $ "typeof"
      _      -> pure $ "(" <> show operator <> ")"

conditionalToEApp ::
  Node' ( test :: Node
        , consequent :: Node
        , alternate :: Node
        ) -> Expression
conditionalToEApp { test, consequent, alternate } = do
  test' <- babylonToClean test
  consequent' <- babylonToClean consequent
  alternate' <- babylonToClean alternate
  pure $ EApp (EApp (EApp (EPrim Cond) test') consequent') alternate'

binaryExpressionToEApp :: BinaryExpression' ( operator :: BinaryOperator ) -> Expression
binaryExpressionToEApp { left, right, operator } = do
  left' <- babylonToClean left
  right' <- babylonToClean right
  operator' <- binopToEVar operator
  pure $ EApp (EApp operator' left') right'
    where
      unsupportedMessage = "Unsupported binary operator " <> show operator
      binopToEVar op = case op of
        Equals       -> throwError unsupportedMessage
        NotEquals    -> throwError unsupportedMessage
        In           -> throwError unsupportedMessage
        Instanceof   -> throwError unsupportedMessage
        Pipe         -> throwError unsupportedMessage
        _            -> pure $ EVar $ "(" <> show op <> ")"

identifierToEVar :: forall r. { name :: String | r }-> Expression
identifierToEVar { name } = pure $ EVar name

literalToEPrim :: forall a r. (a -> Prim) -> { value :: a | r } -> Expression
literalToEPrim ctor { value } = pure $ EPrim $ ctor value

callToEApp :: forall r. { arguments :: Array Node, callee :: Node | r } -> Expression
callToEApp { arguments, callee } = case arguments of
  [arg] -> EApp <$> babylonToClean callee <*> babylonToClean arg
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
  foldr letDeclaratorReducer (returnToELet ret) decls' where
    returnToELet = case _ of
      Just arg -> babylonToClean arg
      Nothing  -> throwError "Functions must return values."


type DeclaratorRecord = { id :: String, init :: Maybe Node }

programBodyToELet :: Array Node -> Expression
programBodyToELet declarations = case declarations of
  [] -> throwError "Programs must contains declarations"
  _  -> do
    decls <- variableDeclarationsToDeclarators declarations
    let d = case last decls of
          Nothing -> throwError $ "Impossible state!"
          Just { id } -> pure $ EVar id
    foldr letDeclaratorReducer d decls

variableDeclarationsToDeclarators :: Array Node -> Except String (Array DeclaratorRecord)
variableDeclarationsToDeclarators ns = join <$> (traverse go ns) where
  fromDeclarator = case _ of
    VariableDeclarator { id: (Identifier { name: id })
                       , init
                       } -> pure { id, init }

    _                    -> throwError
                            "A `let` declaration must bind an expression to an identifier"

  exportToDeclarators { declaration, specifiers } = case specifiers of
    [] -> case declaration of
      Nothing -> throwError "Named exports must include a `let` declaration"
      Just d  -> go d
    _  -> throwError "Export specifiers are not allowed"

  go = case _ of
    VariableDeclaration { kind
                        , declarations
                        }
      | kind == Let -> traverse fromDeclarator declarations
      | otherwise   -> throwError $
                       "Invalid declaration type "
                       <> show kind
                       <> ". Only `let` declarations are allowed"

    ExportNamedDeclaration e -> exportToDeclarators e
    ImportDeclaration      i -> pure []

    d               -> throwError $
                       "Invalid statement "
                       <> show d
                       <> ". Only `let` and `return` statements are allowed."

letDeclaratorReducer :: DeclaratorRecord -> Expression -> Expression
letDeclaratorReducer { id, init } acc = case init of
  Nothing    -> throwError "`let` declarations must be initialized"
  Just init' -> ELet id <$> babylonToClean init' <*> acc
