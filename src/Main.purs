module Main where

import Prelude

import Babylon.Types as B
import Clean (runTypeInference, typeInferModule)
import Clean.Expressions (fileToModule)
import Clean.Types (Exp, Type, Module)
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

jsToClean :: String -> Either String Module
jsToClean = extract <<< runExceptT <<< go B.parse'
  where
    go parse js = do
      ast <- relaxF $ parse js
      fileToModule ast

infer :: forall e. String -> Eff (console :: CONSOLE | e) (Either String Type)
infer src =
  case jsToClean src of
    Left err -> pure $ Left $ "JS error: " <> err
    Right exp -> do
      Tuple r _ <- runTypeInference (typeInferModule exp)
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

