
postulate A : Set

data Bool : Set where
  true false : Bool

id : Bool -> Bool
id x = x

id2 : Bool -> Bool -> Bool -> Bool
id2 x = \y -> \z -> x

matteo : (Bool -> Bool) -> Bool -> Bool
matteo f b = f b

luca : Bool -> Bool
luca = (matteo id)

nikos : Bool
nikos = luca true

xor : Bool → Bool → Bool
xor = λ { true  true  → false
        ; false false → false
        ; true false  → true
        ; false true  → true
        }

-- not : Bool -> Bool
-- not true = false
-- not false = true

-- data Prova : Set where
--   p1 p2 p3 p4 : Prova

-- pippo : Prova -> Bool
-- pippo p1 = true
-- pippo p2 = false
-- pippo p3 = true
-- pippo p4 = false

main = nikos