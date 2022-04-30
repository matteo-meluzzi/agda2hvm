
-- postulate A : Set

data Bool : Set where
  True False : Bool

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

-- _+_ : Nat -> Nat -> Nat
-- Z + b = b
-- (S a) + b = S (a + b) 

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

-- map : {A B : Set} -> (A -> B) -> List A -> List B
-- map f Nil = Nil
-- map f (Cons x xs) = Cons (f x) (map f xs)

map : (Bool -> Bool) -> List Bool -> List Bool
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)


data Pair (A B : Set) : Set where
  P  : A -> B -> Pair A B

-- nikos : Bool
-- nikos = luca true

data Friends : Set where
  Matteo Nikos Luca Andrei : Friends

-- friend : Friends -> Bool
-- friend Matteo = False
-- friend Luca = True
-- friend Nikos = True
-- friend Andrei = True

friend : Friends -> Friends -> Bool
friend a Matteo = False
friend Luca Matteo = True
friend Nikos Matteo = True
friend Andrei Matteo = True
friend _ _ = False


not : Bool -> Bool
not True = False
not False = True

and : Bool -> Bool -> Bool
and True True = True
and _ _ = False

and3 : Bool -> Bool -> Bool -> Bool
and3 True a True = True
and3 a b True = True
and3 _ _ _ = False

-- xor : Bool → Bool → Bool
-- xor = λ { true  true  → false
--         ; false false → false
--         ; true false  → true
--         ; false true  → true
--         }

-- data Prova : Set where
--   p1 p2 p3 p4 : Prova

-- pippo : Prova -> Bool
-- pippo p1 = True
-- pippo p2 = False
-- pippo p3 = True
-- pippo p4 = False

main = map not (Cons True (Cons False Nil))


-- (Nil_0) = Nil

-- (Cons_0) = @a @b (Cons_2 a b)
-- (Cons_2 a b) = (Cons a b)

-- (Main) = ((Cons_0) True ((Cons_0) False Nil))