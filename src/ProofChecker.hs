module ProofChecker
    ( unify
    ) where

import Data.Map (Map)
import Data.Text (Text)

unify :: Text -> Text -> Maybe (Map Text Text)
unify _ _ = Nothing
