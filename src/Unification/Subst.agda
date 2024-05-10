module Unification.Subst where

open import Data.Nat
open import Data.Fin
open import Unification.Term
open import Unification.OccurCheck
open import Data.Product

data AList : (m n : ℕ) → Set where
  anil : {n : ℕ} → AList n n
  _asnoc_/_
    : { m n : ℕ}
    → AList m n
    → Term m
    → Fin (suc m)
    --------------------
    → AList (suc m) n

sub : {m n : ℕ} → AList m n → (Fin m → Term n)
sub anil = ι
sub (σ asnoc t' / x) = (sub σ) ◇ (t' for x)