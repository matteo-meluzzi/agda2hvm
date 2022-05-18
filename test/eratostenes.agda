open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

{-# NON_TERMINATING #-}
range : Nat -> Nat -> Nat -> List Nat
range bot top step = if bot < top then Cons bot (range (bot + step) top step) else Nil

inList : List Nat -> Nat -> Bool
inList (Cons y ys) x = if x == y then true else false
inList Nil x = false

listDiff : List Nat -> List Nat -> List Nat
listDiff (Cons x xs) ys = if inList ys x then listDiff xs ys else Cons x (listDiff xs ys)
listDiff Nil ys = Nil

{-# NON_TERMINATING #-}
primesTo : Nat -> List Nat
primesTo n = sieve (range 2 n 1)
             where
                sieve : List Nat -> List Nat
                sieve (Cons x xs) = Cons x (sieve (listDiff xs (range x n x)))
                sieve Nil = Nil

main : Nat -> List Nat
main n = primesTo n