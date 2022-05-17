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

first :: [a] -> a
first xs = head xs

second :: [a] -> a
second xs = xs !! 1

third :: [a] -> a
third xs = xs !! 2

fourth :: [a] -> a
fourth xs = xs !! 3