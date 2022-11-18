{-# LANGUAGE QuasiQuotes #-}
module ParserSpec (spec) where

import Prelude hiding (Ordering(..))
import Data.Text.Lazy qualified as T
import Test.Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec (parse, ErrorFancy(ErrorFail))
import NeatInterpolation (text)

import Types hiding (ex)
import Parser


spec :: SpecWith ()
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
      "ANNEAB+NECD" `parsesTo` AN [Fun NE "AB", Fun NE "CD"]
    it "parses OR functor" $
      "ORNEAB|NECD" `parsesTo` OR [Fun NE "AB", Fun NE "CD"]
    it "parses NO functor" $
      "NONEAB" `parsesTo` NO (Fun NE "AB")

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
      "NEAB /\\ NECD" `parsesTo` AN [Fun NE "AB", Fun NE "CD"]
    it "parses OR functor" $
      "NEAB \\/ NECD" `parsesTo` OR [Fun NE "AB", Fun NE "CD"]
    it "parses NO functor" $
      "~(NEAB \\/ NECD)"
        `parsesTo`
          NO (OR [Fun NE "AB", Fun NE "CD"])

  describe "proposition" $ do
    let parsesTo a b = parse propWithInfo "" a `shouldParse` b
    it "parses a proposition without file" $
      "lemma\txxx\t`EQ A B ==> ?X. EQ B X`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop [Fun EQ "AB"] "X" (Fun EQ "BX")
          , Nothing
          )
    it "parses a proposition without context" $
      "lemma\txxx\t`EQ a a`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop [] "" (Fun EQ "aa")
          , Nothing
          )
    it "parses complex proposition" $
      "cn\tx\t`PG A B C D /\\ BE A E D ==> ?X. BE B X D /\\ BE C X E`\tfile.prf"
        `parsesTo`
          ( "cn:x"
          , Prop 
            [Fun PG "ABCD", Fun BE "AED"]
            "X"
            (AN [Fun BE "BXD", Fun BE "CXE"])
          , Just "file.prf"
          )

  describe "definition" $ do
    let parsesTo a b = parse propWithInfo "" a `shouldParse` b
    it "parses simple definition" $
      "unequal\t`NE A B <=> ~(EQ A B)`"
        `parsesTo`
          ("defn:unequal"
          , Prop [Fun NE "AB"] "" (NO (Fun EQ "AB"))
          , Nothing
          )

  describe "proof" $ do
    let parsesTo a b = parse proofBlock "" a `shouldParse` b
    it "parses inferred expression" $
      "EEACac" `parsesTo` Infer (Fun EE "ACac") ""
    it "parses inferred expression with reference" $
      "EEAAab  cn:equalitysub"
        `parsesTo`
          (Infer (Fun EE "AAab") "cn:equalitysub")

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
          [ (Fun EQ "BA", [Infer (Fun EQ "ab") "axiom:nullsegment1"])
          , (Fun NE "BA", [Infer (Fun EE "bcac") "cn:equalitysub"])
          ]

    it "parses proof by contradiction" $
      parsesTo
        (T.fromStrict [text|
          COCBA   assumption
           COABC  lemma:collinearorder
          NCCBA   reductio
        |])
        $ Reductio (Fun CO "CBA") (Fun NC "CBA")
          [Infer (Fun CO "ABC") "lemma:collinearorder"]
