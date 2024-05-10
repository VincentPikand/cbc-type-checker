module Unification.Unify where

open import Unification.Term
open import Unification.OccurCheck
open import Unification.Subst
open import Data.Nat
open import Data.Fin
open import Data.Maybe
open import Data.Product


flexFlex : {m : ℕ} → Fin m → Fin m → ∃ (AList m)
flexFlex {suc m} x y with thick x y
... | just y' = (m , anil asnoc ι y' / x)
... | no = (suc m , anil)

flexRigid : {m : ℕ} → Fin m → Term m → Maybe (∃ (AList m))
flexRigid {suc m} x t with check x t
... | just t' = just (m , anil asnoc t' / x)
... | nothing = nothing
 
amgu : {m : ℕ} → (t₁ t₂ : Term m) → ∃ (AList m) → Maybe (∃ (AList m))
amgu leaf leaf acc = just acc
amgu leaf (t₁ fork t₂) _ = nothing
amgu (s₁ fork s₂) leaf _ = nothing
amgu (s₁ fork s₂) (t₁ fork t₂) acc = do
  acc' ← amgu s₁ t₁ acc
  amgu s₂ t₂ acc'
amgu (ι x) (ι y) (m , anil) = just (flexFlex x y)
amgu (ι x) t (m , anil) = flexRigid x t
amgu t (ι y) (m , anil) = flexRigid y t
amgu s t (n , σ asnoc r / z) = do
  (m , σ') ← amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
  just ((m , (σ' asnoc r / z)))
  
unify : {m : ℕ} → Term m → Term m → Maybe (∃ (AList m))
unify {m} s t = amgu s t (m , anil)
