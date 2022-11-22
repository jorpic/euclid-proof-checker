module ProofCheckerSpec (spec) where

import Prelude hiding (Ordering(..))
import Data.Map.Strict qualified as Map
import Test.Hspec

import Types
import ProofChecker

spec :: Spec
spec = do
  describe "mergeVars" $ do
    it "merges when no conflicts"
      $ mergeVars
        [ Map.fromList [('a','b'), ('b','b')]
        , Map.fromList [('a','b')]
        ]
      `shouldBe`
        Right (Map.fromList [('a','b'), ('b','b')])
    it "fails if there are conflicts"
      $ mergeVars
        [ Map.fromList [('a','b'), ('b','b')]
        , Map.fromList [('a','c')]
        ]
      `shouldBe`
        Left "conflicting mappings: ('a',('c','b'))"

  describe "matchEx" $ do
    it "fails when functors does not match"
      $ matchEx
        (Fun EQ "AB") (Fun NE "AB")
      `shouldBe`
        Left "can't match Fun EQ \"AB\" with Fun NE \"AB\""
    it "fails when variables clash"
      $ matchEx
        (Fun EQ "AA") (Fun EQ "AB")
      `shouldBe`
        Left "conflicting mappings: ('A',('B','A'))"
    it "ok when no conflict "
      $ matchEx
        (Fun EQ "AB") (Fun EQ "BA")
      `shouldBe`
        Right (Map.fromList [('A','B'), ('B','A')])
