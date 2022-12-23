{-# LANGUAGE TemplateHaskell #-}
module ProofChecker
  ( Facts
  , ProofContext(..)
  , checkProof
  , rewriteAs
  , mergeVars
  ) where

import Control.Monad (foldM, zipWithM, (>=>))
import Data.Either (rights)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Set qualified as Set

import Types

type Facts = Map PropName Prop
type VarMap = Map Char Char

-- | Check a proof of a proposition.
-- The proof can reference some of already proved facts.
-- Returns error if proof is not valid.
checkProof :: Facts -> Prop -> Proof -> Either String ()
checkProof facts (Prop{..}) proof = do
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
      | otherwise -> Left "Proof does not match prop's consequent"
    [] -> Left "No proved expressions! The proof was empty?"


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


checkBlock :: Facts -> ProofContext -> ProofBlock -> Either String Expr
checkBlock facts cxt@(ProofContext{..}) = \case
  -- Search the exact expr in the context.
  Infer expr ""
    | expr `elem` provedExprs -> pure expr
    | otherwise -> Left "can't infer expression from the context"

  -- Search the referenced proposition among facts and try to satisfy it from
  -- the context.
  Infer expr ref -> case Map.lookup ref facts of
    Nothing -> Left "can't find the referenced statement"
    Just prop -> inferWithProp cxt prop expr

  -- Reductio Expr Expr Proof
  -- Cases Expr [(Expr, Proof)]
  _ -> Left "not implemented yet"


inferWithProp :: ProofContext -> Prop -> Expr -> Either String Expr
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
    [] -> Left "can't prove prop from the context"

  -- New objects may be introduced by the proposition.
  -- Rename them according to 'extendedVarMap'.
  let newObjects = catMaybes $ map (`Map.lookup` extendedVarMap) existentialVars
  -- ^ 'catMaybes' is fine here because 'Nothing' occurs only if there is
  -- some variable that is mentioned in 'existentialVars' but not used in
  -- the antecedent.

  if any (`Set.member` knownObjects) newObjects
    then Left $ "Some of the new objects clash with known ones: "
      ++ show newObjects
    else pure consequent


-- In the provided context search all expressions that can be matched to `ex` without
-- a conflict with the var map `vm`.
searchEx :: [Expr] -> VarMap -> Expr -> [VarMap]
searchEx cxt vm ex
  = rights
  $ map ((ex `rewriteAs`) >=> mergeVars vm) cxt


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
rewriteAs :: Expr -> Expr -> Either String VarMap
rewriteAs ex1 ex2 = case (ex1, ex2) of
  (AN xs, AN ys) | length xs == length ys -> rewriteMany xs ys
  (OR xs, OR ys) | length xs == length ys -> rewriteMany xs ys
  (Fun f xs, Fun g ys)
    | f == g && length xs == length ys
      -> mergeMany $ zipWith Map.singleton xs ys
  _ -> Left $ "can't match " ++ show ex1 ++ " with " ++ show ex2
  where
    mergeMany = foldM mergeVars Map.empty
    rewriteMany xs ys = zipWithM rewriteAs xs ys >>= mergeMany


-- Merges list of mappings.
-- Fails if there are conflicts in mappings
-- (e.g. [a->b] in one mapping and [a->c] in another).
mergeVars :: VarMap -> VarMap -> Either String VarMap
mergeVars vm = foldM f vm . Map.toList
  where
    f m (k,x) = case Map.lookup k m of
      Nothing -> pure $ Map.insert k x m
      Just y
        | x == y -> pure m
        | otherwise -> Left $ "conflicting mappings: " ++ show (k, (x, y))
