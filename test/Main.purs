module Test.Main where

import Prelude

import Babylon.Types (Node)
import Babylon.Types as B
import Clean (defaultEnv, runTypeInference, typeInference)
import Clean.Types (Exp(..), Prim(..))
import Clean.Expressions (babylonToClean)
import Control.Comonad (extract)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Except (Except, runExceptT, withExceptT)
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Foreign (F)
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
     (EApp (EApp (EVar "id") (EVar "id")) (EPrim (LNumber 2.0)))

e4 :: Exp
e4 = ELet "id" (EAbs "x" (EApp (EVar "x") (EVar "x")))
     (EVar "id")

e5 :: Exp
e5 = EAbs "m" (ELet "y" (EVar "m")
               (ELet "x" (EApp (EVar "y") (EPrim (LBoolean true)))
                (EVar "x")))

jsToClean :: (String -> F Node) -> String -> Except String Exp
jsToClean parse js = do
  ast <- relaxF $ parse js
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
  let exprs = [ "42"
              , "true"
              , "'hello'"
              , "!false"
              , "!42"
              , "1 + 2"
              , "1 + false"
              , "true ? 1 : 0"
              , "false ? 1 : 'zero'"
              , "x => x"
              , "x => y => x"
              , "a => b => c => c ? b : typeof a + b"
              , """
                a => b => {
                  let c = a + b,
                      d = true;
                  return d ? c : a;
                }
                """
              , "(x => x) (42)"
              , "(x => y => x) (42)"
              , "(x => y => x) ('hello')"
              ]
  traverse_ (go B.parseExpression') exprs

  let stmts = [ "let x = 42;"
              , """
                let id = x => x;
                let y = id(42);
                """
              , """
                let sub = x => y => x - y;
                let x = sub ('string') (1);
                """
              ]
  traverse_ (go B.parse') stmts

  let modules = [ """
                  export let foo = 42;
                  """
                , """
                  import foo from 'foo'; // import statements get erased and there must be something in a program
                  let bar = 42;
                  """
                ]
  traverse_ (go B.parse') modules

  let records = [ "let e = {};"
                , "let r = {'a': 1};"
                , "let r = {b: 2};"
                , "let r = {a: 'a', b: 2};"
                , """
                  let r = {a: 1};
                  let i = r.a;
                  """
                ]
  traverse_ (go B.parse') records

  go B.parse' """
let arr = [1,2,3,4,5];
              """

  where
    go parser s = case extract $ runExceptT $ jsToClean parser s of
      Left err -> log $ "JS error: " <> err
      Right exp -> test exp

relaxF :: F ~> Except String
relaxF = withExceptT $ foldr append "" <<< (show <$> _)
