{-# OPTIONS --guardedness #-}


open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe

open import Data.Nat.Show using (show; readMaybe)
open import Data.List.Base using (head; drop)
open import Data.Maybe.Base using (fromMaybe)
open import Data.String.Base using (unwords)
open import IO
open import Function.Base using (_$_)

open import System.Environment

data MyList (A : Set) : Set where
  Nil : MyList A
  Cons : A → MyList A → MyList A

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

{-# NON_TERMINATING #-}
range : Nat -> Nat -> Nat -> MyList Nat
range bot top step = if bot < top then Cons bot (range (bot + step) top step) else Nil

inList : MyList Nat -> Nat -> Bool
inList (Cons y ys) x = if x == y then true else false
inList Nil x = false

listDiff : MyList Nat -> MyList Nat -> MyList Nat
listDiff (Cons x xs) ys = if inList ys x then listDiff xs ys else Cons x (listDiff xs ys)
listDiff Nil ys = Nil

{-# NON_TERMINATING #-}
primesTo : Nat -> MyList Nat
primesTo n = sieve (range 2 n 1)
             where
                sieve : MyList Nat -> MyList Nat
                sieve (Cons x xs) = Cons x (sieve (listDiff xs (range x n x)))
                sieve Nil = Nil

at : MyList Nat -> Nat -> Nat
at (Cons x xs) zero    = x
at (Cons x xs) (suc n) = at xs n
at Nil       m       = 0

last : {A : Set} -> MyList A -> Maybe A
last (Cons x Nil) = just x 
last (Cons x xs) = last xs
last Nil = nothing

main : Main
main = run $ do
  args <- getArgs
  let nstr = fromMaybe "0" (head args)
  let n = fromMaybe 0 (readMaybe 10 nstr)
  let res = fromMaybe 0 $ last (primesTo n)
   
  putStrLn (show res)