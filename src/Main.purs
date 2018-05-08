module Main where

import Prelude

import Babylon.Types as B
import Clean (defaultEnv, runTypeInference, typeInference)
import Clean.Expressions (babylonToClean)
import Clean.Types (Exp, Type)
import Control.Comonad (extract)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Except (Except, runExceptT, withExceptT)
import Data.Either (Either(..), either)
import Data.Foldable (foldr)
import Data.Foreign (F)
import Data.List (length)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Data.Validation.Semigroup (unV)
import Node.Buffer (BUFFER, toString)
import Node.Encoding (Encoding(..))
import Node.FS (FS)
import Node.FS.Sync (readFile)
import Node.Optlicative (Opt(Opt), Optlicative, Preferences, logErrors, optlicate, string)
import Node.Process (PROCESS)

type Config = { file :: String }

myConfig :: { file :: Config -> Opt Config (file :: String)}
myConfig = { file: Opt parseConfig }

showConfig :: Config -> String
showConfig { file } =
  "file: " <> file

parseConfig :: Optlicative Config
parseConfig = {file: _} <$> string "file" Nothing

myPrefs :: Preferences Config
myPrefs = { errorOnUnrecognizedOpts: false, usage: Nothing, globalOpts: parseConfig }

main :: forall e. Eff (buffer :: BUFFER, exception :: EXCEPTION, fs :: FS, process :: PROCESS, console :: CONSOLE | e) Unit
main = do
  { cmd, value } <- optlicate {} myPrefs
  maybe
    (log "")
    (\x -> log "Path parsed" *> log x)
    cmd
  unV
    (\x -> do
      log "Errors found: "
      log (show (length x) <> " errors")
      logErrors x)
    (\{file}-> do
      buff <- readFile file
      src <- toString UTF8 buff
      result <- infer src
      logResults src result)
    value

jsToClean :: forall e. String -> Either String Exp
jsToClean = extract <<< runExceptT <<< go B.parse'
  where
    go :: (String -> F B.Node) -> String -> Except String Exp
    go parse js = do
      ast <- relaxF $ parse js
      babylonToClean ast

infer :: forall e. String -> Eff (console :: CONSOLE | e) (Either String Type)
infer src =
  case jsToClean src of
    Left err -> pure $ Left $ "JS error: " <> err
    Right exp -> do
      Tuple r _ <- runTypeInference (typeInference defaultEnv exp)
      pure r

showClean :: Either String Exp -> String
showClean = either id show

relaxF :: F ~> Except String
relaxF = withExceptT $ foldr append "" <<< (show <$> _)

logResults :: forall e a. Show a => String -> (Either String a) -> Eff (console :: CONSOLE | e) Unit
logResults src result = do
  case result of
    Left err -> log $ "error: " <> err <> " in\n\n" <> src
    Right t  -> log $ src <> " :: " <> show t



