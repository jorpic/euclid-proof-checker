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
        (Map.fromList [('a','b'), ('b','b')])
        (Map.fromList [('a','b')])
      `shouldBe`
        Right (Map.fromList [('a','b'), ('b','b')])
    it "fails if there are conflicts"
      $ mergeVars
        (Map.fromList [('a','b'), ('b','b')])
        (Map.fromList [('a','c')])
      `shouldBe`
        Left "conflicting mappings: ('a',('c','b'))"

  describe "rewriteAs" $ do
    it "fails when functors does not match"
      $ rewriteAs
        (Fun EQ "AB") (Fun NE "AB")
      `shouldBe`
        Left "can't match Fun EQ \"AB\" with Fun NE \"AB\""
    it "fails when variables clash"
      $ rewriteAs
        (Fun EQ "AA") (Fun EQ "AB")
      `shouldBe`
        Left "conflicting mappings: ('A',('B','A'))"
    it "ok when no conflict "
      $ rewriteAs
        (Fun EQ "AB") (Fun EQ "BA")
      `shouldBe`
        Right (Map.fromList [('A','B'), ('B','A')])

  describe "checkProp" $ do
    let eq = Fun EQ
    it "infers expression from context" $ do
      let cxt = [ eq "xy" , eq "yZ", eq "XY" , eq "YZ" , eq "XX" ]
      let target = eq "XZ"
      let prop = Prop [eq "AB", eq "BC", eq "CD"] "" (eq "AD")
      -- AB -> xy
      -- BC ->
      checkProp cxt target prop
        `shouldBe`
          Right (Map.fromList [('A','X'),('B','X'),('C','Y'),('D','Z')])
