module Utils where

mapLeft :: (a -> b) -> Either a r -> Either b r
mapLeft f = either (Left . f) Right

catchEither :: Either e r -> (e -> Either e r) -> Either e r
catchEither e f = either f (const e) e
