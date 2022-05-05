module Utils where

safeTail :: [a] -> [a]
safeTail [] = []
safeTail xs = tail xs

safeInit :: [a] -> [a]
safeInit [] = []
safeInit xs = init xs

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead xs = Just $ head xs