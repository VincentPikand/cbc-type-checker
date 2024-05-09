module Unification.OccurCheck where

open import Data.Nat
open import Data.Fin
open import Data.Maybe

thin : {n : ℕ} → (x : Fin (suc n)) → (y : Fin n) → Fin (suc n)
thin zero y = suc y 
thin (suc x) zero = zero 
thin (suc x) (suc y) = suc (thin x y)

thick : {m : ℕ} → (x y : Fin (suc m)) → Maybe (Fin m)
thick zero zero = nothing -- x = y
thick zero (suc y) = just y -- y > x
thick {zero} (suc ()) zero
thick {suc m} (suc x) zero = just zero -- y < x
thick {zero} (suc ()) (suc y)
thick {suc m} (suc x) (suc y) with thick {m} x y
... | just x′ = just (suc x′)
... | nothing = nothing -- x = y