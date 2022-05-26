{-# OPTIONS --guardedness #-}


open import Agda.Builtin.Nat

open import Data.Nat.Show using (show; readMaybe)
open import Data.List.Base using (head; drop)
open import Data.Maybe.Base using (fromMaybe)
open import Data.String.Base using (unwords)
open import IO
open import Function.Base using (_$_)

open import System.Environment

comp : {A : Set } -> Nat -> (A -> A) -> A -> A
comp 0 f x = f x
comp (suc n) f x = comp n (\x -> f (f x)) x

main : Main
main = run $ do
  args <- getArgs
  let nstr = fromMaybe "0" (head args)
  let n = fromMaybe 0 (readMaybe 10 nstr)
  let res = comp n (\x -> x) 0
   
  putStrLn (show res)
