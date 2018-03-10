module Test.Main where

import Prelude

import Clean (runTypeInference, typeInference)
import Clean.Expressions (Exp(..), Lit(..))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Either (Either(..))
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

test :: forall e. Exp -> Eff (console :: CONSOLE | e) Unit
test e = do
  Tuple res _ <- runTypeInference (typeInference Map.empty e)
  case res of
    Left err -> log $ "error: " <> err
    Right t  -> log $ show e <> " :: " <> show t

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  traverse_ test [e0, e1, e2, e3, e4, e5]
