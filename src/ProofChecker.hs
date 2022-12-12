module ProofChecker
  ( Facts
  , checkProof
  , checkProp
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
type Objs = Set Char
type VarMap = Map Char Char

checkProof :: Facts -> Prop -> Proof -> Either String ()
checkProof facts (Prop{..}) proof = proofLoop from proof
 -- get objects from antecendent
 -- proofLoop
 -- unify with conclusion and check existentials
  where
    proofLoop cxt = \case
      [] -> Left "proof is empty"
      _ -> Left "proof checker is not implemented"


-- Some properties contain existential quantification in the consequent, that
-- means that new objects should be created and added to the set of known
-- objects.
checkBlock :: Facts -> Objs -> [Expr] -> ProofBlock -> Either String ()
checkBlock facts objs cxt = \case
  Infer expr ""
    | expr `elem` cxt -> Right ()
    | otherwise -> Left "can't infer expression from the context"
    -- search the exact expr in the context
  Infer expr ref -> case Map.lookup ref facts of
    Nothing -> Left "can't find referenced statement"
    Just prop -> do
      varMap <- checkProp cxt expr prop
      let freeVars = ex prop
      let freeVars' = catMaybes $ map (`Map.lookup` varMap) freeVars -- why `catMaybes` is ok?
      case filter (`Set.member` objs) freeVars' of
        [] -> pure ()
        vs -> Left $ "conflicting free variables" ++ show vs
  _ -> Left "not implemented yet"


checkProp :: [Expr] -> Expr -> Prop -> Either String VarMap
checkProp cxt tgt (Prop{..}) = do
  vMap <- to `rewriteAs` tgt
  case foldM (searchEx cxt) vMap from of -- list monad inside foldM
    vm : _ -> pure vm
    [] -> Left "can't prove prop from context"


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
