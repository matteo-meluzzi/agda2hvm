
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

main = nikos