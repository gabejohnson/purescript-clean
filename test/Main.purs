module Test.Main where

import Prelude

import Babylon.Types as B
import Clean (defaultEnv, runTypeInference, typeInference)
import Clean.Expressions (Exp(..), Lit(..), babylonToClean)
import Control.Comonad (extract)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Except (Except, runExceptT, withExceptT)
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Foreign (F)
import Data.Map as Map
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))

e0 :: Exp
e0 = ELet "id" (EAbs "x" (EVar "x"))
     (EVar "id")

e1 :: Exp
e1 = ELet "id" (EAbs "x" (EVar "x"))
     (EApp (EVar "id") (EVar "id"))

e2 :: Exp
e2 = ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
     (EApp (EVar "id") (EVar "id"))

e3 :: Exp
e3 = ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
     (EApp (EApp (EVar "id") (EVar "id")) (ELit (LNumber 2.0)))

e4 :: Exp
e4 = ELet "id" (EAbs "x" (EApp (EVar "x") (EVar "x")))
     (EVar "id")

e5 :: Exp
e5 = EAbs "m" (ELet "y" (EVar "m")
               (ELet "x" (EApp (EVar "y") (ELit (LBoolean true)))
                (EVar "x")))

jsToClean :: forall e. String -> Except String Exp
jsToClean js = do
  ast <- relaxF $ B.parseExpression' js
  babylonToClean ast

logResults :: forall e a. Show a => Exp -> (Either String a) -> Eff (console :: CONSOLE | e) Unit
logResults e r = do
  case r of
    Left err -> log $ "error: " <> err
    Right t  -> log $ show e <> " :: " <> show t


test :: forall e. Exp -> Eff (console :: CONSOLE | e) Unit
test e = do
  Tuple r _ <- runTypeInference (typeInference defaultEnv e)
  logResults e r

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- Test a Clean expression
  traverse_ test [e0, e1, e2, e3, e4, e5]

  -- Test JS
  let res = extract $ runExceptT $ jsToClean "a => b => { let c = 1; let d = a + b + c; return d}"
  case res of
    Left err -> log $ "JS error: " <> err
    Right exp -> test exp

relaxF :: F ~> Except String
relaxF = withExceptT $ foldr append "" <<< (show <$> _)
