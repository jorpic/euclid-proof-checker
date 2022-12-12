module Main (main) where

import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.Map.Strict qualified as Map
import System.Environment (getArgs)
import System.FilePath ((</>))

import Types
import Parser qualified
import ProofChecker (Facts, checkProof)

data AnyErr = StringException String
  deriving Show

instance Exception AnyErr

main :: IO ()
main = getArgs >>= \case
  [proofDir] -> main' proofDir
    `catch` (\(StringException e) -> putStrLn e)
  _ -> putStrLn "help!"

main' :: FilePath -> IO ()
main' proofDir = do
  defs <- tryX $ Parser.props $ proofDir </> "Definitions.txt"
  props <- tryX $ Parser.props $ proofDir </> "Theorems.txt"

  evalStateT
    (mapM_ (checkProp proofDir) $ defs ++ props)
    $ ProverState Map.empty


data ProverState = ProverState
  { provedFacts :: Facts
  }

checkProp :: FilePath -> PropWithInfo -> StateT ProverState IO ()
checkProp proofDir (name, prop, proofFile) = do
  facts <- gets provedFacts
  whenJust proofFile $ \file -> do
    liftIO $ print name
    tryX
      $ checkProof facts prop
      <$> tryX (Parser.proof $ proofDir </> file)
  modify (\s -> s {provedFacts = Map.insert name prop facts})

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = flip $ maybe (pure ())

tryX :: MonadIO m => m (Either String b) -> m b
tryX f =  f >>= either (liftIO . throwIO . StringException) pure
