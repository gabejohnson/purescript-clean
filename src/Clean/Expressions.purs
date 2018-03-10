module Clean.Expressions (Exp(..), Lit(..)) where

import Babylon.Types as B
import Data.Either (Either(..))
import Prelude (class Eq, class Ord, class Show, bind, pure, show, ($), (<>))

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
    LNumber n  -> show n
    LBoolean b -> if b then "true" else "false"
    LString s -> s

