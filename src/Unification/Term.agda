module Unification.Term where

open import Data.Nat
open import Data.Fin
open import Function

data Term_ (n : ℕ) : Set where
  ι : (x : Fin n) → Term n
  leaf : Term n
  _fork_ : (s t : Term n) → Term n

-- ▹ turns a renaming into a substitution
▹ : {m n : ℕ} → (r : Fin m → Fin n) → Fin m → Term n
▹ r = ι ∘ r

-- ◃ applies a substitution to a term
_◃_ : {m n : ℕ} → (Fin m → Term n) → Term m → Term n
f ◃ (ι x) = f x
f ◃ leaf = leaf
f ◃ (s fork t) = (f ◃ s) fork (f ◃ t)

_◇_ 
  : {m n l : ℕ} 
  → (f : Fin m → Term n) → (g : Fin l → Term m)
  ----------------------------------------------
  → Fin l → Term n
f ◇ g = λ x → f ◃ (g x)