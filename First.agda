
-- postulate A : Set

data Bool : Set where
  True False : Bool

-- id : Bool -> Bool
-- id x = x

-- id2 : Bool -> Bool -> Bool -> Bool
-- id2 x = \y -> \z -> x

-- matteo : (Bool -> Bool) -> Bool -> Bool
-- matteo f b = f b

-- luca : Bool -> Bool
-- luca a = (matteo id) a

data List (A : Set) : Set where
  Nil   : List A
  Cons  : A -> List A -> List A

-- nikos : Bool
-- nikos = luca true

-- not : Bool -> Bool
-- not true = false
-- not false = true

-- xor : Bool → Bool → Bool
-- xor = λ { true  true  → false
--         ; false false → false
--         ; true false  → true
--         ; false true  → true
--         }

-- data Prova : Set where
--   p1 p2 p3 p4 : Prova

-- pippo : Prova -> Bool
-- pippo p1 = true
-- pippo p2 = false
-- pippo p3 = true
-- pippo p4 = false

main = {!   !}


-- (Nil_0) = Nil

-- (Cons_0) = @a @b (Cons_2 a b)
-- (Cons_2 a b) = (Cons a b)

-- (Main) = ((Cons_0) True ((Cons_0) False Nil))