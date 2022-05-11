
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Data.Nat.Show

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

variable A B : Set

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

filter : (A → Bool) → List A → List A
filter p Nil = Nil
filter p (Cons x xs) = if p x then (Cons x (filter p xs)) else filter p xs

append : List A → List A → List A
append Nil ys = ys
append (Cons x xs) ys = (Cons x (append xs ys))

_or_ : Bool -> Bool -> Bool
true or _ = true
_ or true = true
_ or _ = false

qsort : List Nat -> List Nat
qsort Nil = Nil
qsort (Cons x xs) = let smaller = filter (\y -> y < x) xs
                        bigger = filter (\y -> (x < y) or (x == y)) xs 
                    in
                        append (append smaller (Cons x Nil)) bigger

range : Nat -> List Nat
range 0 = Cons 0 Nil
range m@(suc n) = Cons m (range n)

at : List Nat -> Nat -> Nat
at (Cons x xs) Zero    = x
at (Cons x xs) (suc n) = at xs n
at Nil         m       = 0

main : IO ⊤
main = do
  let n = 10000
  let res = at (qsort (range n)) n
  putStrLn (show res)
