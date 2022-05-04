
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

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

bind : List A → (A → List B) → List B
bind Nil f = Nil
bind (Cons x xs) f = append (f x) (bind xs f)

range : Nat → Nat → List Nat
range x y = go ((suc y) - x) x
  where
    go : Nat → Nat → List Nat
    go zero    _ = Nil
    go (suc m) n = Cons n (go m (suc n))

record Triple : Set where
  constructor triple
  field
    fst snd trd : Nat

alltriples : Nat → List Triple
alltriples top = (bind (range 1 top) (λ z → (bind (range 1 z) (λ y → (bind (range 1 y) (λ x → (Cons (triple x y z) Nil)))))))

cartesian : Triple → Bool
cartesian (triple x y z) = x * x + y * y == z * z

triples : Nat → List Triple
triples top = filter cartesian (alltriples top)

sumall : List Triple → Nat
sumall Nil = 0
sumall (Cons (triple x y z) xs) = x + y + z + sumall xs

test1 = sumall (triples 20) -- evaluates to 33638

main = test1