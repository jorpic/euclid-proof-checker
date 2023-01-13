{-# LANGUAGE QuasiQuotes #-}
module ParserSpec (spec) where

import Prelude hiding (Ordering(..))
import Data.Text.Lazy qualified as T
import Test.Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec (parse, ErrorFancy(ErrorFail))
import NeatInterpolation (text)

import Types
import Parser
import TestUtils () -- for instance IsString Expr


spec :: Spec
spec = do
  describe "exprCC" $ do
    let parsesTo a b = parse exprCC "" a `shouldParse` b
    it "parses single functor" $
      "LTABCD" `parsesTo` Fun LT "ABCD"
    it "checks functor arity" $
      parse exprCC "" "LTABCDEF"
        `shouldFailWith`
          errFancy 8 (fancy
            $ ErrorFail "expected 4 arguments for functor LT")
    it "parses AND functor" $
      "ANNEAB+NECD" `parsesTo` AN ["NEAB", "NECD"]
    it "parses OR functor" $
      "ORNEAB|NECD" `parsesTo` OR ["NEAB", "NECD"]
    it "parses NO functor" $
      "NONEAB" `parsesTo` NO "NEAB"

  describe "exprHR" $ do
    let parsesTo a b = parse exprHR "" a `shouldParse` b
    it "parses single functor without spaces" $
      "LTABCD" `parsesTo` Fun LT "ABCD"
    it "parses single functor with spaces" $
      "LT A B C D" `parsesTo` Fun LT "ABCD"
    it "checks functor arity" $
      parse exprCC "" "LTABCDEF"
        `shouldFailWith`
          errFancy 8 (fancy
            $ ErrorFail "expected 4 arguments for functor LT")
    it "parses AND functor" $
      "NEAB /\\ NECD" `parsesTo` AN ["NEAB", "NECD"]
    it "parses OR functor" $
      "NEAB \\/ NECD" `parsesTo` OR ["NEAB", "NECD"]
    it "parses NO functor" $
      "~(NEAB \\/ NECD)"
        `parsesTo`
          NO (OR ["NEAB", "NECD"])

  describe "proposition" $ do
    let parsesTo a b = parse propWithInfo "" a `shouldParse` b
    it "parses a proposition without file" $
      "lemma\txxx\t`EQ A B ==> ?X. EQ B X`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop ["EQAB"] "X" "EQBX" False
          , Nothing
          )
    it "parses a proposition without context" $
      "lemma\txxx\t`EQ a a`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop [] "" "EQaa" False
          , Nothing
          )
    it "parses complex proposition" $
      "cn\tx\t`PG A B C D /\\ BE A E D ==> ?X. BE B X D /\\ BE C X E`\tfile.prf"
        `parsesTo`
          ( "cn:x"
          , Prop 
            ["PGABCD", "BEAED"]
            "X"
            (AN ["BEBXD", "BECXE"])
            False
          , Just "file.prf"
          )

  describe "definition" $ do
    let parsesTo a b = parse propWithInfo "" a `shouldParse` b
    it "parses simple definition" $
      "unequal\t`NE A B <=> ~(EQ A B)`"
        `parsesTo`
          ("defn:unequal"
          , Prop ["NEAB"] "" (NO "EQAB") True
          , Nothing
          )

  describe "definition with OR" $ do
    let parsesTo a b = parse propWithInfo "" a `shouldParse` b
    it "parses simple definition" $
      "xxx\t`CO A B C <=> (EQ A B \\/ EQ B C)`"
        `parsesTo`
          ("defn:xxx"
          , Prop ["COABC"] "" (OR ["EQAB", "EQBC"]) True
          , Nothing
          )

  describe "proof" $ do
    let parsesTo a b = parse proofBlock "" a `shouldParse` b
    it "parses inferred expression" $
      "EEACac" `parsesTo` Infer "EEACac" ""
    it "parses inferred expression with reference" $
      "EEAAab  cn:equalitysub"
        `parsesTo`
          (Infer "EEAAab" "cn:equalitysub")

    it "parses proof by cases" $
      parsesTo
        (T.fromStrict [text|
          cases EEBCbc:EQBA|NEBA
           case 1: EQBA
            EQab    axiom:nullsegment1
           qedcase
           case 2: NEBA
            EEbcac   cn:equalitysub
           qedcase
          EEBCbc  cases
        |])
        $ Cases (Fun EE "BCbc")
          [ ("EQBA", [Infer "EQab"   "axiom:nullsegment1"])
          , ("NEBA", [Infer "EEbcac" "cn:equalitysub"])
          ]

    it "parses proof by contradiction" $
      parsesTo
        (T.fromStrict [text|
          COCBA   assumption
           COABC  lemma:collinearorder
          NCCBA   reductio
        |])
        $ Reductio "COCBA" "NCCBA"
          [Infer "COABC" "lemma:collinearorder"]
