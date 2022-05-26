{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Function.Base using (_$_)
open import IO
open import System.Environment
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe.Base using (fromMaybe)
open import Data.List.Base using (head; drop)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

filter : {A : Set} -> (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then (x ∷ (filter p xs)) else filter p xs

append : {A : Set} -> List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = (x ∷ (append xs ys))

_or_ : Bool -> Bool -> Bool
true or _ = true
_ or true = true
_ or _ = false

qsort : List Nat -> List Nat
qsort [] = []
qsort (x ∷ xs) =  let smaller = filter (\y -> y < x) xs
                      bigger = filter (\y -> (x < y) or (x == y)) xs 
                  in
                      append (append smaller (x ∷ [])) bigger

range : Nat -> List Nat
range 0 = 0 ∷ []
range top@(suc n) = top ∷ (range n)

last : List Nat -> Nat
last (x ∷ []]) = x
last (x ∷ xs) = last xs
last [] = 0 

main : Main
main = run $ do
  args <- getArgs
  let nstr = fromMaybe "10000" (head args)
  let n = fromMaybe 10000 (readMaybe 10 nstr)
  let res = last (qsort (range n))
  putStrLn (show res)
 