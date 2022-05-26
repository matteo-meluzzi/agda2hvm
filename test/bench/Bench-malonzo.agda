{-# OPTIONS --guardedness #-}


open import Agda.Builtin.Nat

open import Data.Nat.Show using (show; readMaybe)
open import Data.List.Base using (head; drop)
open import Data.Maybe.Base using (fromMaybe)
open import Data.String.Base using (unwords)
open import IO
open import Function.Base using (_$_)

open import System.Environment


-- A binary tree of uints
data Tree : Set where 
    Node : Tree -> Tree -> Tree
    Leaf : Nat -> Tree

-- Creates a tree with 2^n elements
gen : Nat -> Tree
gen 0 = Leaf 1
gen (suc n) = Node (gen(n)) (gen(n))

-- Adds all elements of a tree
sun : Tree -> Nat
sun (Leaf x)   = 1
sun (Node a b) = sun a + sun b

-- Performs 2^n additions
main : Main
main = run $ do
  args <- getArgs
  let nstr = fromMaybe "0" (head args)
  let n = fromMaybe 0 (readMaybe 10 nstr)
  let res = sun (gen n)
   
  putStrLn (show res)
