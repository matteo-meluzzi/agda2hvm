open import Agda.Builtin.Nat

fib : Nat -> Nat
fib 0 = 0
fib 1 = 1
fib (suc n@(suc m)) = fib n + fib m

main : Nat -> Nat
main n = fib n