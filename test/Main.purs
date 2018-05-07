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

-- infinite type
e4 :: Exp
e4 = ELet "foo" (EAbs "f" (EApp (EVar "f") (EVar "f")))
               (EVar "foo")

e5 :: Exp
e5 = EAbs "m" (ELet "y" (EVar "m")
               (ELet "x" (EApp (EVar "y") (EPrim (LBoolean true)))
                (EVar "x")))

b :: Exp
b = EApp (EApp (EPrim $ RecordExtend "b") (EPrim $ LString "foo")) (EPrim RecordEmpty)

a :: Exp
a = EApp (EApp (EPrim $ RecordExtend "a") (EPrim $ LNumber 1.0)) b

s :: Exp
s = EApp (EPrim $ RecordSelect "b") a

e6 :: Exp
e6 = ELet "r1" s s

e7 :: Exp
e7 = ELet "r" (EApp (EPrim (RecordSelect "b"))
                    (EApp (EApp (EPrim (RecordExtend "a"))
                                (EPrim (LNumber 1.0)))
                          (EApp (EApp (EPrim (RecordExtend "b"))
                                      (EPrim (LNumber 2.0)))
                                (EPrim (RecordEmpty)))))
              (EVar "r")

jsToClean :: (String -> F Node) -> String -> Except String Exp
jsToClean parse js = do
  ast <- relaxF $ parse js
  babylonToClean ast

logResults :: forall e a. Show a => String -> Exp -> (Either String a) -> Eff (console :: CONSOLE | e) Unit
logResults s e r = do
  log case r of
    Left err -> "error: " <> err <> " in:\n\t" <> s <> "\n" <> show e <> "\n"
    Right t  -> show t <> "\n"

logExpResults :: forall e a. Show a => Exp -> (Either String a) -> Eff (console :: CONSOLE | e) Unit
logExpResults e r = do
  log case r of
    Left err -> "error: " <> err <> " in:\n\t" <> show e <> "\n"
    Right t  -> show t <> "\n"



test :: forall e. String -> Exp -> Eff (console :: CONSOLE | e) Unit
test s e = do
  Tuple r _ <- runTypeInference (typeInference defaultEnv e)
  logResults s e r

testExp :: forall e. Exp -> Eff (console :: CONSOLE | e) Unit
testExp e = do
  Tuple r _ <- runTypeInference (typeInference defaultEnv e)
  logExpResults e r

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- Test a Clean expression
  traverse_ testExp [e0, e1, e2, e3, e4, e5, e6, e7]

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
              , "let foo = f => f(f);"
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


  let arrays = [ "let xs = [];"
               , "let xs = []; let ys = []; let zs = [];" -- checking for fresh type variables
               , "let xs = [1,2,3,4,5];"
               , "let xs = [1,2,'3',4,5];"
               , "let xs = [[1], [1]];"
               , "let xs = [[true], [1]];"
               , "let xs = [{a: 1, b: 2}, {a: 3, b: 4}];"
               , "let xs = [{a: 1, b: 2}, {b: 3, a: 4}];"
               , """
                 let r1 = {a:1, b: 'foo', c: true};
                 let a = r1.b;
                 """
               , "let b = ({a:1, b: 'foo', c: true}).b"
               , "let f = x => x.a + x.b;"
               ]
  traverse_ (go B.parse') arrays

  where
    go parser s = case extract $ runExceptT $ jsToClean parser s of
      Left err -> log $ "JS error: " <> err
      Right exp -> test s exp

relaxF :: F ~> Except String
relaxF = withExceptT $ foldr append "" <<< (show <$> _)
