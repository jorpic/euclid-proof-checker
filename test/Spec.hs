{-# LANGUAGE DeriveGeneric #-}

import Control.Monad (forM_)
import Data.Aeson qualified as Aeson
import Data.Map (Map)
import Data.Text (Text)
import Data.Text qualified as T
import Data.ByteString.Lazy.Char8 qualified as B (lines, readFile)
import GHC.Generics
import Test.Hspec

import ProofChecker (parseExpr, unify')

data UnificationExample = UnificationExample
  { p :: Text
  , q :: [Text]
  , res :: Maybe (Map Char Char)
  } deriving (Show, Generic)

instance Aeson.FromJSON UnificationExample

-- FIXME: add hand-made unification tests

main :: IO ()
main = do
  -- this file was generated from tracing ./CheckProofs.php
  jsonl <- B.lines <$> B.readFile "test/unification.jsonl"

  hspec $ describe "unify"
    $ forM_ jsonl $ \json -> maybe
      (specify "..."
        $ expectationFailure $ "invalid JSON in " <> show json)
      unificationSpec
      (Aeson.decode json)

unificationSpec :: UnificationExample -> SpecWith ()
unificationSpec (UnificationExample{..})
  = specify (show p <> " ~ " <> show q) $ do
    let res' = do
          p' <- parseExpr $ T.unpack p
          q' <- sequence $ map (parseExpr . T.unpack) q
          pure $ unify' p' q'
    case res' of
      Left err -> expectationFailure err
      Right atomMapping -> atomMapping `shouldBe` res
