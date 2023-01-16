module ProofCheckerSpec (spec) where

import Prelude hiding (Ordering(..))
import Data.Map.Strict qualified as Map
import Test.Hspec

import Types
import ProofChecker
import TestUtils () -- for instance IsString Expr

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
        Left (StringErr ["conflicting mappings: ('a',('c','b'))"])

  describe "rewriteAs" $ do
    it "fails when functors does not match"
      $ rewriteAs "EQAB" "NEAB"
      `shouldBe`
        Left (StringErr ["can't match EQAB with NEAB"])
    it "fails when variables clash"
      $ rewriteAs "EQAA" "EQAB"
      `shouldBe`
        Left (StringErr ["conflicting mappings: ('A',('B','A'))"])
    it "ok when no conflict"
      $ rewriteAs "EQAB" "EQBA"
      `shouldBe`
        Right (Map.fromList [('A','B'), ('B','A')])

--   describe "rewriteAs'" $ do
--     it "ok when no conflict"
--       $ rewriteAs' "EQAB" "EQBA"
--       `shouldBe`
--         Right (Map.fromList [('A','B'), ('B','A')])
--     it "ok when matching AN with AN"
--       $ rewriteAs' "ANEQBX+EQXA" "ANEQBA+EQAC"
--       `shouldBe`
--         Right (Map.fromList [('B','B'), ('X','A'), ('A', 'C')])
--     it "ok when matching AN with it's subexpr"
--       $ rewriteAs' "ANEQBX+EQXA" "EQBA"
--       `shouldBe`
--         Right (Map.fromList [('B','B'), ('X','A')])
--     it "fails when matching OR with it's subexpr"
--       $ rewriteAs' "OREQBX|EQXA" "EQBA"
--       `shouldBe`
--         Left (StringErr ["can't match OR[EQBX,EQXA] with EQBA"])
--     it "ok when matching subexpr with OR"
--       $ rewriteAs' "EQBA" "OREQBX|EQXA"
--       `shouldBe`
--         Right (Map.fromList [('A','X'), ('B','B')])
--     it "fails when matching subexpr with AN"
--       $ rewriteAs' "EQBA" "ANEQBX+EQXA"
--       `shouldBe`
--         Left (StringErr ["can't match EQBA with AN[EQBX,EQXA]"])


  let can = (`shouldBe` Right ())
  let can't = (`shouldNotBe` Right ())

  describe "inferExact" $ do
    let cxt = ["BEXYZ", "BEABC", "BEDFG", "BEFGH"]
    it "finds expr in context"
      $ can $ inferExact cxt "BEDFG"
    it "can't find subexpressions of AN"
      $ can't $ inferExact cxt "ANBEDFG+BEFGH"

  describe "inferExact'" $ do
    let cxt = ["BEXYZ", "BEABC", "BEDFG","BEFGH"]
    it "finds expr in context"
      $ can $ inferExact' cxt "BEDFG"
    it "can find subexpressions of AN"
      $ can $ inferExact' cxt "ANBEDFG+BEFGH"
    it "can find subexpressions of OR"
      $ can $ inferExact' cxt "ORBEDFG|BEQWE"

  describe "inferWithEqs" $ do
    let cxt = ["EQAX", "EQYB", "BEAWY", "COABX"]
    it "find expr with equality substitutions"
      $ can $ inferWithEqs cxt "BEXWB"
    it "can't find subexpr"
      $ can't $ inferWithEqs cxt "ANBEXWB+COXYX"

  describe "inferWithEqs'" $ do
    let cxt = ["EQAX", "EQYB", "BEAWY", "COABX"]
    it "can find subexpr of AN"
      $ can $ inferWithEqs' cxt "ANBEXWB+COXYX"
    it "can find subexpr of OR"
      $ can $ inferWithEqs' cxt "ORBEZXC|COXYX"
    it "can find deeply nested subexpr of AN"
      $ can $ inferWithEqs' cxt "ANBEXWB+ORBEZXC|COXYX"
    it "can find deeply nested subexpr of OR"
      $ can $ inferWithEqs' cxt (OR ["ANBEXWB+COXYX", "BEZXC"])

  describe "inferWithProp'" $ do
    let cxt = ["BEXYZ"]
    it "can use conjunct in consequent"
      $ can $ inferWithProp'
        cxt
        (Prop ["BEABC"] "" "ANNEBC+NEAB+NEAC" False)
        "NEXY"

--    - we have BEXYZ in the context
--    - we want to prove NEXY using prop BEABC => AN[NEBC,NEAB,NEAC]
--    - it is sufficient to match NEAB with NEXY
--
--    AN + OR
