open import Agda.Builtin.Nat

g : {A : Set} -> (A -> A) -> A -> A
g f x = f (f x)

main : Nat -> Nat
main n = g (λ n → n * 2) n