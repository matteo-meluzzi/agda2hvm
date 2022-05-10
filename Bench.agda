open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

-- A binary tree of uints
data Tree : Set where 
    Node : Tree -> Tree -> Tree
    Leaf : Nat -> Tree

-- Creates a tree with 2^n elements
gen : Nat -> Tree
gen 0 = Leaf 1
gen (suc n) = Node (gen(n)) (gen(n))

-- Adds all elements of a tree
sun : Tree -> Nat
sun (Leaf x)   = 1
sun (Node a b) = sun a + sun b

-- Performs 2^n additions
-- main = sun (gen 10)