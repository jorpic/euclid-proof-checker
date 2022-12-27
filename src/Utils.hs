module Utils where

mapLeft :: (a -> b) -> Either a r -> Either b r
mapLeft f = either (Left . f) Right
