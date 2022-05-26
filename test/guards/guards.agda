data Bool : Set where
  true false : Bool

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

filter : {A : Set} → (A → Bool) → List A → List A
filter p Nil = Nil
filter p (Cons x xs) with p x
filter p (Cons x xs)    | true  = Cons x (filter p xs)
filter p (Cons x xs)    | false = filter p xs

main : Bool -> List Bool
main n = filter (\_ -> true) Nil