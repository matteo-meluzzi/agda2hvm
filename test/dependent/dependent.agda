open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List

data U : Set where
  nat : U
  bool : U
  list : U → U

⟦_⟧ : U → Set
⟦ nat ⟧ = Nat
⟦ bool ⟧ = Bool
⟦ list t ⟧ = List ⟦ t ⟧

f : (c : U) → ⟦ c ⟧ → ⟦ c ⟧
f nat      zero     = zero
f nat      (suc x)  = x
f bool     false    = true
f bool     true     = false
f (list c) []       = []
f (list c) (x ∷ xs) = f c x ∷ f (list c) xs

test₁ = f nat 42

test₂ = f (list (list bool)) ((true ∷ false ∷ []) ∷ (false ∷ []) ∷ [])