
open import Agda.Builtin.Nat

infixr 5 _::_
data Vector (A : Set) : Nat → Set where
    [] : Vector A zero
    _::_ : {n : Nat} → A → Vector A n → Vector A (suc n)

head : {A : Set}{n : Nat} -> Vector A (suc n) -> A
head (x :: xs) = x
