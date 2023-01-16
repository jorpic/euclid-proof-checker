module Utils where

import Data.Either (lefts, rights)
import Control.Exception (Exception)

data ProofCheckerErr = StringErr { errs ::  [String] }
  deriving (Eq, Exception)

instance Show ProofCheckerErr where
  show = unlines . zipWith indent [0..] . errs
    where
      indent i = (replicate (i*2) ' ' ++)

type Result a = Either ProofCheckerErr a


throwStr :: String -> Result a
throwStr = Left . StringErr . (:[])

-- FIXME: withErrContext should never wrap a whole function body,
-- instead function call should be wrapped as in that case it is easier to add
-- higher-level details to the err context.
withErrContext :: String -> Result a -> Result a
withErrContext cxt = mapLeft $ StringErr . (cxt:) . errs


mapLeft :: (a -> b) -> Either a r -> Either b r
mapLeft f = either (Left . f) Right

orElse :: Either e r -> (e -> Either e r) -> Either e r
orElse e f = either f (const e) e

anyE :: [Result a] -> Result a
anyE xs = case rights xs of
  []  -> throwStr "all failed"
  x:_ -> pure x

allE :: [Result a] -> Result ()
allE xs = case lefts xs of
  []  -> pure ()
  e:_ -> Left e
