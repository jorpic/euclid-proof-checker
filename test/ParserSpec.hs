module ParserSpec (spec) where

import Prelude hiding (Ordering(..))
import Test.Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec (parse, ErrorFancy(ErrorFail))

import Types hiding (ex)
import Parser


spec :: SpecWith ()
spec = do
  describe "exprCC" $ do
    let parsesTo a b = parse exprCC "" a `shouldParse` b
    it "parses single functor" $
      "LTABCD" `parsesTo` ex LT "ABCD"
    it "checks functor arity" $
      parse exprCC "" "LTABCDEF"
        `shouldFailWith`
          errFancy 8 (fancy
            $ ErrorFail "number of arguments does not match functor arity")
    it "parses AND functor" $
      "ANNEAB+NECD" `parsesTo` Expr AN [ex NE "AB", ex NE "CD"]
    it "parses OR functor" $
      "ORNEAB|NECD" `parsesTo` Expr OR [ex NE "AB", ex NE "CD"]
    it "parses NO functor" $
      "NONEAB" `parsesTo` Expr NO [ex NE "AB"]

  describe "exprHR" $ do
    let parsesTo a b = parse exprHR "" a `shouldParse` b
    it "parses single functor without spaces" $
      "LTABCD" `parsesTo` ex LT "ABCD"
    it "parses single functor with spaces" $
      "LT A B C D" `parsesTo` ex LT "ABCD"
    it "checks functor arity" $
      parse exprCC "" "LTABCDEF"
        `shouldFailWith`
          errFancy 8 (fancy
            $ ErrorFail "number of arguments does not match functor arity")
    it "parses AND functor" $
      "NEAB /\\ NECD" `parsesTo` Expr AN [ex NE "AB", ex NE "CD"]
    it "parses OR functor" $
      "NEAB \\/ NECD" `parsesTo` Expr OR [ex NE "AB", ex NE "CD"]
    it "parses NO functor" $
      "~(NEAB \\/ NECD)"
        `parsesTo`
          Expr NO [Expr OR [ex NE "AB", ex NE "CD"]]

  describe "proposition" $ do
    let parsesTo a b = parse prop' "" a `shouldParse` b
    it "parses a proposition without file" $
      "lemma\txxx\t`EQ A B ==> ?X. EQ B X`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop Implication [ex EQ "AB"] "X" (ex EQ "BX")
          , Nothing
          )
    it "parses a proposition without context" $
      "lemma\txxx\t`EQ a a`\t"
        `parsesTo`
          ( "lemma:xxx"
          , Prop Implication [] "" (ex EQ "aa")
          , Nothing
          )
    it "parses complex proposition" $
      "cn\tx\t`PG A B C D /\\ BE A E D ==> ?X. BE B X D /\\ BE C X E`\tfile.prf"
        `parsesTo`
          ( "cn:x"
          , Prop Implication
            [ex PG "ABCD", ex BE "AED"]
            "X"
            (Expr AN [ex BE "BXD", ex BE "CXE"])
          , Just "file.prf"
          )

  describe "definition" $ do
    let parsesTo a b = parse def' "" a `shouldParse` b
    it "parses simple definition" $
      "unequal\t`NE A B <=> ~(EQ A B)`"
        `parsesTo`
          ("unequal"
          , Prop Equivalence [ex NE "AB"] "" (Expr NO [ex EQ "AB"])
          )

ex :: Fn -> String -> Expr
ex fn = Expr fn . map Atom
