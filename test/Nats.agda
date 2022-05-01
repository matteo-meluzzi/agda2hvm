
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Builtin.Bool

plus3 : Nat → Nat
plus3 n = suc (suc (suc n))

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

test1 = pred (suc (pred (plus3 40)))

twice : Nat → Nat
twice n = 2 * n

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = twice (pow2 n)

consume : Nat → Nat
consume zero = zero
consume (suc n) = consume n

fac : Nat -> Nat
fac zero = 1
fac n@(suc prev) = n * (fac prev) 

fib : Nat -> Nat
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n


if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

ifte = if true then 1 else 0

test2 = consume (pow2 24)

main = fib 40 -- HVM: 6.5 s