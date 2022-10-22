{-# LANGUAGE DeriveGeneric #-}

import Test.Hspec
import Data.Aeson qualified as Aeson
import Data.Maybe (catMaybes)
import Data.Map (Map)
import Data.Text (Text)
import Data.ByteString.Lazy.Char8 qualified as B (lines, readFile)
import GHC.Generics

import ProofChecker (unify)

data UnificationExample = UnificationExample
  { p, q :: Text
  , assume :: [Text]
  , result :: Map Text Text
  } deriving (Show, Generic)

instance Aeson.FromJSON UnificationExample


main :: IO ()
main = do
  jsn <- catMaybes . map Aeson.decode . B.lines
    --vv this file was generated from tracing ./CheckProofs.php
    <$> B.readFile "test/unification.jsonl"
  hspec $ describe "unification" $ do
    let spec (UnificationExample{..})
          = specify (show p <> " ~ " <> show q)
            $ unify p q `shouldBe` Just result
    mapM_ spec jsn
