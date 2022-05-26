
open import Agda.Builtin.Nat

comp : {A : Set } -> Nat -> (A -> A) -> A -> A
comp 0 f x = f x
comp (suc n) f x = comp n (\x -> f (f x)) x

main : Nat -> Nat
main n = comp n (\x -> x) 0