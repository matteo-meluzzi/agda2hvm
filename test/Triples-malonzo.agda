
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Function.Base using (_$_)
open import IO
open import System.Environment
open import Data.Nat.Show using (show; readMaybe)
open import Data.Maybe.Base using (fromMaybe)
open import Data.List.Base using (head; drop)

variable A B : Set

data MyList (A : Set) : Set where
  [] : MyList A
  _::_ : A → MyList A → MyList A

infixr 5 _::_

if_then_else_ : Bool → A → A → A
if true  then x else y = x
if false then x else y = y

id : A → A
id x = x

filter : (A → Bool) → MyList A → MyList A
filter p [] = []
filter p (x :: xs) = (if p x then (x ::_) else id) (filter p xs)

_++_ : MyList A → MyList A → MyList A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_my>>=_ : MyList A → (A → MyList B) → MyList B
[]        my>>= f = []
(x :: xs) my>>= f = f x ++ (xs my>>= f)

range : Nat → Nat → MyList Nat
range x y = go (suc y - x) x
  where
    go : Nat → Nat → MyList Nat
    go zero    _ = []
    go (suc m) n = n :: go m (suc n)

record Triple : Set where
  constructor triple
  field fst snd trd : Nat

alltriples : Nat → MyList Triple
alltriples top = range 1 top my>>= λ z → range 1 z my>>= λ y → range 1 y my>>= λ x → (triple x y z) :: []

pythagorean : Triple → Bool
pythagorean (triple x y z) = x * x + y * y == z * z

triples : Nat → MyList Triple
triples top = filter pythagorean (alltriples top)

sumall : MyList Triple → Nat
sumall [] = 0
sumall (triple x y z :: xs) = x + y + z + sumall xs

test1 = sumall (triples 200) -- evaluates to 33638

main : Main
main = run $ do
  args <- getArgs
  let nstr = fromMaybe "10000" (head args)
  let n = fromMaybe 10000 (readMaybe 10 nstr)
  let res = sumall (triples n)
  putStrLn (show res)
