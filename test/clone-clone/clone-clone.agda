open import Agda.Builtin.Nat

g : {A : Set} -> (A -> A) -> A -> A
g f x = f (f x)

q : {A : Set} -> (A -> A) -> A -> A
q f x = f x

m : Nat -> Nat
m a = 1 + a
 
main : Nat -> Nat
main n = g g (\x -> x + 3) 4