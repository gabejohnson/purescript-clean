module Clean.Expressions (babylonToClean, fileToModule) where

import Babylon.Types (BinaryExpression', BinaryOperator(Pipe, Instanceof, In, NotEquals, Equals), Node(..), Node', UnaryOperator(Typeof, Plus, Minus, Void, Delete, Throw), VariableKind(Let))
import Clean.Types (Exp(ELet, EVar, EAbs, EApp, EPrim), Prim(Cond, LString, RecordEmpty, RecordExtend, RecordSelect, LArray, LBoolean, LNumber))
import Clean.Types as CT
import Control.Monad.Except (Except, throwError)
import Data.Array (last, length, unsnoc)
import Data.Foldable (foldr)
import Data.List as L
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (sequence, traverse)
import Prelude (bind, join, otherwise, pure, show, ($), (<$>), (<*>), (<<<), (<>), (==))


type Expression = Except String Exp

fileToModule :: Node -> Except String CT.Module
fileToModule = case _ of
  File { program: Program { body } }
    -> case body of
     []    -> throwError "Modules must node be empty"
     decls -> sequence $ L.fromFoldable $ declToDecl <$> decls
  _ -> throwError "Files must be files"

declToDecl :: Node -> Except String CT.Declaration
declToDecl = case _ of
  ImportDeclaration imp      -> importToDeclaration imp
  ExportNamedDeclaration exp -> exportToDeclaration exp
  VariableDeclaration decl   -> variableToDeclaration decl
  d                          -> throwError $ "Unsupported declaration type " <> show d
  where
    importToDeclaration { source, specifiers } = do
      src <- babylonToClean source
      specs <- traverse babylonToClean specifiers
      pure $ CT.ImportDeclaration (L.fromFoldable specs) src

    exportToDeclaration { declaration
                        , source
                        , specifiers
                        } = case declaration, source, specifiers of
      Just decl, Nothing, [] -> declToDecl decl
      _, _, _                -> throwError $ "Unsupported export declaration"

    variableToDeclaration { declarations, kind } = case kind of
      Let -> case declarations of
        [VariableDeclarator { id: Identifier { name }, init }]
               -> CT.VariableDeclaration <$> (declaratorToELet name init)
        _      -> throwError $ "Exactly ONE declarator allowed at the top-level. "
                  <> show (length declarations)
                  <> " provided."
      _ -> throwError $ "Unsupported variable declaration type: " <> show kind
      where
        declaratorToELet :: String -> Maybe Node -> Expression
        declaratorToELet name init = case init of
          Just init' -> let result = (babylonToClean init')
                        in ELet name <$> result <*> result
          Nothing    -> throwError "`let` declarations must be initialized"

babylonToClean :: Node -> Expression
babylonToClean = case _ of
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
objectToRecord { properties } = foldr go (pure $ EPrim RecordEmpty) properties
  where
    go n acc = case n of
      ObjectProperty { key, value } -> do
        k <- babylonToClean key
        v <- babylonToClean value
        r <- acc
        maybe (throwError $ "Unsupported label type: " <> show r)
              (\l -> pure $ EApp (EApp (EPrim $ RecordExtend l) v) r)
          $ propertyToString k
      _ -> throwError $ "Unsupported label type: " <> show n

propertyToString :: Exp -> Maybe String
propertyToString = case _ of
  EPrim (LString s) -> Just s
  EVar s            -> Just s
  _                 -> Nothing

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

variableDeclarationsToDeclarators :: Array Node -> Except String (Array DeclaratorRecord)
variableDeclarationsToDeclarators ns = join <$> (traverse go ns) where
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


letDeclaratorReducer :: DeclaratorRecord -> Expression -> Expression
letDeclaratorReducer { id, init } acc = case init of
  Nothing    -> throwError "`let` declarations must be initialized"
  Just init' -> ELet id <$> babylonToClean init' <*> acc
