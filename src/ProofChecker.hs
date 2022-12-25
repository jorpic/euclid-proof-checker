{-# LANGUAGE TemplateHaskell #-}
module ProofChecker
  ( Facts
  , ProofContext(..)
  , checkProof
  , rewriteAs
  , mergeVars
  ) where

import Prelude hiding (Ordering(..))
import Control.Exception
import Control.Monad (foldM, zipWithM, (>=>))
import Data.Either (rights)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Set qualified as Set

import Types
import Utils (mapLeft)

type Facts = Map PropName Prop
type VarMap = Map Char Char

data ProofCheckerErr
  = StringErr String
  | ErrContext String ProofCheckerErr
  deriving Exception

instance Show ProofCheckerErr where
  show = unlines . loop 0
    where
      indent i = (replicate (i*2) ' ' ++)
      loop i = \case
        StringErr err -> [indent i err]
        ErrContext cxt err -> indent i cxt : loop (i+1) err

type Result a = Either ProofCheckerErr a

throwStr :: String -> Result a
throwStr = Left . StringErr

withErrContext :: String -> Result a -> Result a
withErrContext = mapLeft . ErrContext

-- | Check a proof of a proposition.
-- The proof can reference some of already proved facts.
-- Returns error if proof is not valid.
checkProof :: Facts -> Prop -> Proof -> Result ()
checkProof facts p@(Prop{..}) proof
  = withErrContext ("when proving " ++ show p) $ do
    -- Iterate over the proof blocks checking each in the context containing
    -- already proved intermediate expressions.
    let foldProofBlocks cxt chkBlk = foldM chkBlk cxt proof

    -- Initial context contains expressions from antecedent.
    let startCxt = foldr addToContext emptyContext antecedent

    finalCxt <- foldProofBlocks startCxt $ \cxt block -> do
      provedExpr <- checkBlock facts cxt block
      pure $ provedExpr `addToContext` cxt -- Extend the context.

    -- The last proved expression should be equal to the consequent.
    case provedExprs finalCxt of
      lastProvedExpr : _
        | lastProvedExpr == consequent -> pure () -- Success!
        | otherwise -> throwStr "Proof does not match prop's consequent"
      [] -> throwStr "No proved expressions! The proof was empty?"


data ProofContext = ProofContext
  { knownObjects :: Set Char
  , provedExprs :: [Expr]
  }
emptyContext :: ProofContext
emptyContext = ProofContext Set.empty []

addToContext :: Expr -> ProofContext -> ProofContext
addToContext e c = c
  { knownObjects = getObjects e <> knownObjects c
  , provedExprs = e : provedExprs c
  }
  where
    getObjects = foldMap Set.singleton -- Get objects from an expression.

blockSummary :: ProofBlock -> String
blockSummary = \case
  Infer expr _      -> "infer " ++ show expr
  Reductio _ expr _ -> "reductio " ++ show expr
  Cases expr _      -> "case " ++ show expr

checkBlock :: Facts -> ProofContext -> ProofBlock -> Result Expr
checkBlock facts cxt blk
  = withErrContext (blockSummary blk)
  $ case blk of
    -- Search the exact expr in the context.
    Infer expr ""
      | expr `elem` provedExprs cxt -> pure expr
      | otherwise -> throwStr "can't infer expression from the context"

    -- This is a meta-axiom. It searches EQ in context and tries to
    -- apply substitution.
    Infer expr "cn:equalitysub" -> do
      let equalities = concatMap
            (\case { Fun EQ [a,b] -> [(a,b), (b,a)] ; _ -> [] })
            (provedExprs cxt)
      let canBeRewrittenWithEqualities expr' =
            case expr' `rewriteAs` expr of
              Right vm ->
                all (`elem` equalities)
                  $ Map.toList $ Map.filterWithKey (/=) vm
              _ -> False
      if any canBeRewrittenWithEqualities $ provedExprs cxt
        then pure expr
        else withErrContext
          ("equalities found " ++ show equalities)
          $ withErrContext ("provedExprs " ++ show (provedExprs cxt))
          $ throwStr "Can't find how to rewrite with equalities"

    -- Search the referenced proposition among facts and try to satisfy it from
    -- the context.
    Infer expr ref -> case Map.lookup ref facts of
      Nothing -> throwStr "can't find the referenced statement"
      Just prop -> withErrContext ("with ref" ++ show prop)
        $ inferWithProp cxt prop expr

    Reductio assumption conclusion proof -> do
      -- FIXME: check that the assumption equals the conclusion negated
      let foldProofBlocks cx chkBlk = foldM chkBlk cx proof
      finalCxt <- foldProofBlocks (assumption `addToContext` cxt) $ \cxt' block -> do
        provedExpr <- checkBlock facts cxt' block
        pure $ provedExpr `addToContext` cxt' -- Extend the context.
      case provedExprs finalCxt of
        lastProvedExpr : cxt'
          -- last expression in context contradicts something in context
          | any (negated lastProvedExpr ==) cxt' -> pure conclusion -- Success!
          | otherwise -> withErrContext ("lastProvedExpr " ++ show lastProvedExpr)
            $ throwStr "No contradiction found"
        [] -> throwStr "No proved expressions! The reductio was empty?"

    -- Cases Expr [(Expr, Proof)]
    _ -> throwStr "not implemented yet"

inferWithProp :: ProofContext -> Prop -> Expr -> Result Expr
inferWithProp ProofContext{..} Prop{..} expr = do
  -- Variable mapping that unifies 'consequent' with the expression to be
  -- proved.
  varMap <- consequent `rewriteAs` expr

  -- For each expression in 'antecedent', find an expression in the context
  -- such that both can be unified by a variable mapping.
  -- All those mappings must be compatible with each other and with 'varMap'.
  let possibleMappings = foldM (searchEx provedExprs) varMap antecedent
  -- ^ List monad is used to search repeatedly and backtrack in case of conflict.
  extendedVarMap <- case possibleMappings of
    vm : _ -> pure vm
    [] -> withErrContext ("base map " ++ show varMap)
      $ throwStr $ "can't prove prop from context " ++ show provedExprs

  -- New objects may be introduced by the proposition.
  -- Rename them according to 'extendedVarMap'.
  let newObjects = catMaybes $ map (`Map.lookup` extendedVarMap) existentialVars
  -- ^ 'catMaybes' is fine here because 'Nothing' occurs only if there is
  -- some variable that is mentioned in 'existentialVars' but not used in
  -- the antecedent.

  if any (`Set.member` knownObjects) newObjects
    then throwStr $ "Some of the new objects clash with known ones: "
      ++ show newObjects
    else rename extendedVarMap consequent


rename :: VarMap -> Expr -> Result Expr
rename varMap expr = case traverse (`Map.lookup` varMap) expr of
  Just expr' -> pure expr'
  Nothing -> throwStr "Impossible! Failed to apply varMap."


-- In the provided context search all expressions that can be matched to `ex` without
-- a conflict with the var map `vm`.
searchEx :: [Expr] -> VarMap -> Expr -> [VarMap]
searchEx cxt vm ex
  = rights
  $ map ((ex `rewriteAs`) >=> mergeVars vm) cxt


-- | Returns negated version of an expression.
negated :: Expr -> Expr
negated = \case
  AN exprs -> OR $ map negated exprs
  OR exprs -> AN $ map negated exprs
  NO expr -> expr
  Fun EQ xs -> Fun NE xs
  Fun NE xs -> Fun EQ xs
  Fun CO xs -> Fun NC xs
  Fun NC xs -> Fun CO xs
  expr -> NO expr


-- Get a varables to variables mapping that converts from ex1 to ex2.
--  `ex1[varMap] = ex2`.
-- Fails if it is not possible to convert ex1 to ex2 due to:
--  - mismatching functors: EQAB -> NECD
--  - conflicting variables: EQAA -> EQAB
--  NB!: Result of `matchEx` is a mapping which is not always injective.
--    E.g. in `matchEx COABC COXYX  => {A: X, B: Y, C: X}`
--    both A and C map to X.
--    Switching arguments would result in variable conflict (non-deterministic
--    mapping).
rewriteAs :: Expr -> Expr -> Result VarMap
rewriteAs ex1 ex2 = case (ex1, ex2) of
  (AN xs, AN ys) | length xs == length ys -> rewriteMany xs ys
  (OR xs, OR ys) | length xs == length ys -> rewriteMany xs ys
  (NO x,  NO y) -> x `rewriteAs` y
  (Fun f xs, Fun g ys)
    | f == g && length xs == length ys
      -> mergeMany $ zipWith Map.singleton xs ys
  _ -> throwStr $ "can't match " ++ show ex1 ++ " with " ++ show ex2
  where
    mergeMany = foldM mergeVars Map.empty
    rewriteMany xs ys = zipWithM rewriteAs xs ys >>= mergeMany


-- Merges list of mappings.
-- Fails if there are conflicts in mappings
-- (e.g. [a->b] in one mapping and [a->c] in another).
mergeVars :: VarMap -> VarMap -> Result VarMap
mergeVars vm = foldM f vm . Map.toList
  where
    f m (k,x) = case Map.lookup k m of
      Nothing -> pure $ Map.insert k x m
      Just y
        | x == y -> pure m
        | otherwise -> throwStr $ "conflicting mappings: " ++ show (k, (x, y))
