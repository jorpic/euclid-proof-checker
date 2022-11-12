module Parser
  ( listOf'
  , prop'
  , proofBlock
  , exprCC
  , exprHR
  )
  where

import Prelude hiding (lex)
import Control.Monad (void, forM, when)
import Data.Maybe (fromMaybe)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy.IO qualified as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (decimal)

import Types


type Parser a = Parsec Void Text a
type Err = ParseErrorBundle Text Void
type Prop' = (Text, Prop, Maybe FilePath)

listOf' :: Parser a -> FilePath -> IO (Either String [a])
listOf' p f
  = prettifyErr . parse (many $ p <* space) f <$> T.readFile f

prettifyErr :: Either Err a -> Either String a
prettifyErr = either (Left . errorBundlePretty) Right

-- FIXME: expalin that we have two syntaxes for expressions
--  - concise one like this: ANEABAFFAC+IABACF
--  - and human readable like this: ~(LT C D A B) /\ NE A B /\ NE C D

proofBlock :: Parser ProofBlock
proofBlock = space >> choice
  [ kw "cases" *> proofByCases
  , lex exprCC >>= \ex ->
    choice
      [ kw "assumption" >> ln >> proofByContradiction ex
      , kw "reductio" >> fail "reductio without assumption"
      , Infer ex . TS.strip . TS.pack <$> many printChar
      ]
  ]
  where
    proofByCases = do
      goal <- lex exprCC <* lex ":"
      cases <- lex (exprCC `sepBy1` "|") <* ln
      proofs <- forM (zip [1..] cases) ((<* ln) . oneCaseProof)
      goal' <- lex exprCC <* kw "cases"
      when (goal' /= goal)
        $ fail "case conclusion does not match the goal"
      return $ Cases goal proofs

    oneCaseProof :: (Int, Expr) -> Parser (Expr, Proof)
    oneCaseProof (i, ex) = do
      i' <- kw "case" *> lex decimal <* lex ":"
      when (i' /= i)
        $ fail "case numbers must be consecutive"
      ex' <- lex exprCC <* ln
      when (ex' /= ex)
        $ fail "invalid case expression"
      proof <- (proofBlock <* ln) `someTill` (kw "qedcase")
      return (ex, proof)

    proofByContradiction ex = do
      (proof, conclusion) <-
        (proofBlock <* ln) `manyTill_` (try $ lex exprCC <* kw "reductio")
      return $ Reductio ex conclusion proof



exprCC :: Parser Expr
exprCC = do
  count 2 letterChar >>= \case
    "NO" -> NO <$> exprCC
    "AN" -> AN <$> sepBy1 exprCC "+"
    "OR" -> OR <$> sepBy1 exprCC "|"
    fn -> readFnArgs letterChar fn

exprHR :: Parser Expr
exprHR = conjunction <?> "expression"
  where
    conjunction = sepBy1 disjunction (lex "/\\") >>= liftOne AN
    disjunction = sepBy1 simpleExpr (lex "\\/") >>= liftOne OR
    simpleExpr  = negation <|> brackets <|> functor
    negation = NO <$> (lex "~" *> exprHR)
    brackets = lex "(" *> exprHR <* lex ")"
    functor = lex (count 2 letterChar) >>= readFnArgs (lex letterChar)

    liftOne fn = \case
      []  -> fail "impossible!"
      [x] -> pure x
      xs  -> pure $ fn xs

readFnArgs :: Parser Char -> String -> Parser Expr
readFnArgs p s = case reads s of
  [(fn,"")] -> some p >>= \case
    args | length args == arity fn
      -> pure $ Fun fn args
    _ -> fail
      $ "expected " <> show (arity fn)
      <> " arguments for functor " <> show fn
  _ -> fail $ "invalid functor: " <>  show s



prop' :: Parser Prop'
prop' = do
  pType <- choice
    [ "cn"          <* tab
    , "axiom"       <* tab
    , "postulate"   <* tab
    , "proposition" <* tab
    , "lemma"       <* tab
    , pure "defn"
    ]
  pName <- takeWhile1P (Just "name") (/= '\t')
  void tab
  pProp <- lex "`" *> prop <* lex "`" <?> "proposition"
  hspace
  pFile <- optional $ some printChar <* hspace

  return
    ( pType <> ":" <> pName -- FIXME: T.toStrict
    , pProp
    , pFile
    )

exVars :: Parser [Char]
exVars = lex "?" *> some (lex letterChar) <* lex "." <?> "existential"

prop :: Parser Prop
prop = exprHR >>= \ex1 ->
  choice
    [ -- ex1 is an antecedent and we unfold it to form context
      (lex $ "==>" <|>  "<=>")
      >> Prop (unfoldAnd ex1)
        <$> (fromMaybe [] <$> optional exVars)
        <*> exprHR
      -- ex1 is a consequent without context
    , pure $ Prop [] [] ex1
    ]
  where
    unfoldAnd = \case
      AN xs -> xs
      x -> [x]

lex, kw :: Parser a -> Parser a
lex p = p <* skipMany (hidden " ") -- FIXME: hspace?
kw p = lex $ try $ p <* lookAhead (space1 <|> eof)
ln :: Parser ()
ln = eol >> hidden space

linesOf :: Parser a -> Parser [a]
linesOf p = space *> some (p <* (ln <|> lookAhead eof)) <* eof
