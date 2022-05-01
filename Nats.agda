
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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

ifte = if true then 1 else 0

test2 = consume (pow2 24)

main = test1