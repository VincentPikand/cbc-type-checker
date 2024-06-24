{-# OPTIONS --postfix-projections #-}

module _ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Substitution as Sub

module Vec where
  open import Data.Vec public
  open import Data.Vec.Properties public
open Vec using (Vec; []; _∷_; lookup)

open import Function using (id)

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; refl; cong₂; module ≡-Reasoning)
open ≡-Reasoning

infix   4 _↘_
infixl  6 _∙_
infix   8 _≐_
infixr 10 _⇒_

variable
  n m : ℕ

------------------------------------------------------------------------
-- Data structures.

-- Well-scoped terms.

data Exp : ℕ → Set where
  var : (x : Fin n) → Exp n
  abs : (e : Exp (suc n)) → Exp n
  app : (f e : Exp n) → Exp n

-- Type variables.

TyCxt = ℕ

TyVar : (Ξ : TyCxt) → Set
TyVar = Fin

-- Types.

data Ty (Ξ : TyCxt) : Set where
  tyvar : (X : TyVar Ξ) → Ty Ξ
  _⇒_   : (A B : Ty Ξ) → Ty Ξ


-- Typing contexts.

Cxt : (Ξ : TyCxt) (n : ℕ) → Set
Cxt Ξ n = Vec (Ty Ξ) n

variable
  Ξ Ξ' Ξ′ Ξ₁ Ξ₂ : TyCxt
  X Y Z         : TyVar Ξ
  A A′ B B′ C   : Ty Ξ
  Γ Γ' Γ′ Γ₁ Γ₂ : Cxt Ξ n
  x             : Fin n
  e f           : Exp n




data Tm (Γ : Cxt Ξ n) : (e : Exp n) → Ty Ξ → Set where
  var :  Tm Γ (var x) (lookup Γ x)
  app 
    : (t : Tm Γ f (A ⇒ B)) (u : Tm Γ e A) 
    → Tm Γ (app f e) B
  abs : (t : Tm (A ∷ Γ) e B) → Tm Γ (abs e) (A ⇒ B)

-- Constraints (equations)
data Eqs Ξ : Set where
  ε   : Eqs Ξ
  _≐_ : (A B : Ty Ξ) → Eqs Ξ
  _∙_ : (E F : Eqs Ξ) → Eqs Ξ

variable
  E E′ F G : Eqs Ξ

------------------------------------------------------------------------
-- Renamings and substitutions.

-- Renamings.

_⊆_ : (Ξ Ξ₁ : TyCxt) → Set
Ξ ⊆ Ξ₁ = Sub.Sub TyVar Ξ Ξ₁

module R = Sub.VarSubst

variable
  η η' η′ η₁ η₂ : Ξ ⊆ Ξ₁

-- Substitutions.

Subst : (Ξ Ξ₁ : TyCxt) → Set
Subst Ξ Ξ₁ = Sub.Sub Ty Ξ Ξ₁

module ApplySubstitution {T : TyCxt → Set} (l : Sub.Lift T Ty) (open Sub.Lift l) where

  infixl 9 _/_

  _/_ : Ty Ξ → Sub.Sub T Ξ Ξ₁ → Ty Ξ₁
  tyvar x / ρ = lift (Vec.lookup ρ x)
  t₁ ⇒ t₂ / ρ = (t₁ / ρ) ⇒ (t₂ / ρ)

  -- module A = Sub.Application (record { _/_ = _/_ })
  -- open A public hiding (_/_)

tySubst : Sub.TermSubst Ty
tySubst .Sub.TermSubst.var = tyvar
tySubst .Sub.TermSubst.app = ApplySubstitution._/_

module S = Sub.TermSubst tySubst

-- Applications of renamings.

wkTyVar : Ξ ⊆ Ξ₁ → TyVar Ξ → TyVar Ξ₁
wkTyVar = Vec.lookup

wkTy : (η : Ξ ⊆ Ξ₁) → Ty Ξ → Ty Ξ₁
wkTy η A = A S./Var η

wkTy1 : Ty Ξ → Ty (suc Ξ)
wkTy1 = wkTy R.wk

wkCxt : (η : Ξ ⊆ Ξ₁) → Cxt Ξ n → Cxt Ξ₁ n
wkCxt η [] = []
wkCxt η (A ∷ Γ) = wkTy η A ∷ wkCxt η Γ
wkCxt1 : Cxt Ξ n → Cxt (suc Ξ) n
wkCxt1 = wkCxt R.wk

wkEqs : (η : Ξ ⊆ Ξ₁) → Eqs Ξ → Eqs Ξ₁
wkEqs η ε = ε
wkEqs η (A ≐ B) = wkTy η A ≐ wkTy η B
wkEqs η (E ∙ F) = wkEqs η E ∙ wkEqs η F

wkEqs1 : Eqs Ξ → Eqs (suc Ξ)
wkEqs1 = wkEqs R.wk

-- Application of substitutions.

variable
  σ τ : Subst Ξ Ξ₁

subTyVar : Subst Ξ Ξ₁ → TyVar Ξ → Ty Ξ₁
subTyVar σ = Vec.lookup σ

subTy : Subst Ξ Ξ₁ → Ty Ξ → Ty Ξ₁
subTy σ A = A S./ σ

subCxt : Subst Ξ Ξ₁ → Cxt Ξ n → Cxt Ξ₁ n
subCxt σ = Vec.map (subTy σ)

subEqs : Subst Ξ Ξ₁ → Eqs Ξ → Eqs Ξ₁
subEqs σ ε = ε
subEqs σ (A ≐ B) = subTy σ A ≐ subTy σ B
subEqs σ (E ∙ F) = subEqs σ E ∙ subEqs σ F

subSub : Subst Ξ₁ Ξ₂ → Subst Ξ Ξ₁ → Subst Ξ Ξ₂
subSub σ σ′ = σ′ S.⊙ σ

-- Constructions of substitutions.

emptySub : Subst zero zero
emptySub = []

wkSub : Ξ₁ ⊆ Ξ₂ → Subst Ξ Ξ₁ → Subst Ξ Ξ₂
wkSub η σ = Vec.map (wkTy η) σ

wkSub1 : Subst Ξ Ξ₁ → Subst Ξ (suc Ξ₁)
wkSub1 = wkSub R.wk

liftSub : Subst Ξ Ξ₁ → Subst (suc Ξ) (suc Ξ₁)
liftSub σ = σ S.↑

idSub : Subst Ξ Ξ
idSub = S.id

renSub : Ξ ⊆ Ξ₁ → Subst Ξ Ξ₁
renSub = Vec.map tyvar

------------------------------------------------------------------------
-- Constraint-based type inference.

data Inf : (Γ : Cxt Ξ n) (e : Exp n) (η : Ξ ⊆ Ξ₁) (A : Ty Ξ₁) (E : Eqs Ξ₁) → Set where
  var : Inf Γ (var x) R.id (lookup Γ x) ε

  abs : let X =  tyvar zero
     in Inf (X ∷ wkCxt1 Γ) e η A E
      → Inf Γ (abs e) (R.wk R.⊙ η) (wkTy η X ⇒ A) E

  app : Inf Γ f η₁ C E
      → Inf (wkCxt η₁ Γ) e η₂ A F
      → let X   = tyvar zero
            η₂′ = η₂ R.⊙ R.wk
     in Inf Γ (app f e) (η₁ R.⊙ η₂′) X (wkEqs η₂′ E ∙ (wkEqs1 F ∙ (wkTy η₂′ C ≐ wkTy1 A ⇒ X)))

------------------------------------------------------------------------
-- Strengthening (occurrence check).

-- Dropping a type variable.

delete : (X : TyVar Ξ) → TyCxt
delete {Ξ = suc Ξ} zero = Ξ
delete (suc X) = suc (delete X)

-- Strengthening a type variable StrTyVar X Y Z: A "subtraction" Z = Y - X.

data StrTyVar : (X : TyVar Ξ) (Y : TyVar Ξ) (Z : TyVar (delete X)) → Set where
  zero-suc : StrTyVar zero (suc Y) Y
  suc-zero : StrTyVar (suc X) zero zero
  suc-suc  : StrTyVar X Y Z → StrTyVar (suc X) (suc Y) (suc Z)

-- Strengthening a type.

data StrTy : (X : TyVar Ξ) (A : Ty Ξ) (A' : Ty (delete X)) → Set where

  tyvar : StrTyVar X Y Z
        → StrTy X (tyvar Y) (tyvar Z)

  _⇒_   : StrTy X A A′
        → StrTy X B B′
        → StrTy X (A ⇒ B) (A′ ⇒ B′)


-- Singleton substitution from successful occurrence check.

sgSub : (X : TyVar Ξ) (η : delete X ⊆ Ξ') (A : Ty Ξ') → Subst Ξ Ξ'
sgSub (zero)  η       A = A ∷ renSub η
sgSub (suc X) (Y ∷ η) A = tyvar Y ∷ sgSub X η A

open import Data.Product using (Σ ; _,_ ; ∃; Σ-syntax; ∃-syntax)

------------------------------------------------------------------------
-- Solving constraints.

open import Relation.Nullary using (¬_; Dec; yes; no)


data _↘_ : Eqs Ξ → Subst Ξ Ξ₁ → Set where

  ε    : ε ↘ idSub {Ξ = Ξ}

  ⇒E   : A ≐ A′ ∙ B ≐ B′ ↘ σ
       → A ⇒ B ≐ A′ ⇒ B′ ↘ σ

  X≐   : StrTy X A A′
       → tyvar X ≐ A ↘ sgSub X R.id A′

  ≐X   : StrTy X A A′
       → A ≐ tyvar X ↘ sgSub X R.id A′

  X≐X  : ¬ (Σ (TyVar (delete X)) (StrTyVar X Y))
       → tyvar X ≐ tyvar Y ↘ idSub {Ξ = Ξ}

  _∙_  : E ↘ σ
       → subEqs σ F ↘ τ
       → E ∙ F ↘ subSub τ σ

------------------------------------------------------------------------
-- Unification

open import Data.Maybe

--------------------------WITH DATAYPES----------------------------------


thick' : (x y : TyVar Ξ) → Dec (∃[ z ] (StrTyVar x y z))
thick' zero zero = no  (λ ())
thick' zero (suc y) = yes (y , zero-suc)
thick' (suc x) zero = yes (zero , suc-zero)
thick' (suc x) (suc y) with thick' x y
... | yes (x' , p) = yes (suc x' , suc-suc p)
... | no ¬z=y-x = no λ{ (suc z , suc-suc snd) → ¬z=y-x (z , snd)}


check' : (X : TyVar Ξ) → (A : Ty Ξ) → Maybe (Σ (Ty (delete X)) (StrTy X A))
check' X (tyvar Y) with thick' X Y
... | yes (Z , proof) = just (tyvar  Z , tyvar proof)
... | no _ = nothing
check' X (A ⇒ B) = do
  (A' , p₁) <- check' X A
  (B' , p₂) <- check' X B
  just (A' ⇒ B' , p₁ ⇒ p₂)

solve' : (E : Eqs Ξ) → ℕ → Maybe (Σ[ Ξ₁ ∈ TyCxt ] Σ (Subst Ξ Ξ₁) (E ↘_))
solve' _  zero = nothing
solve' {Ξ} ε _ = just (Ξ , idSub , ε)
solve' {Ξ} (tyvar X ≐ tyvar Y) _ with thick' X Y
... | yes (y' , p) = just (delete X , sgSub X R.id (tyvar y') , X≐ (tyvar p))
... | no neg-p = just (Ξ , idSub , X≐X neg-p)
solve' (tyvar X ≐ A) _ = do
  (A' , p) ← check' X A
  just (delete X , (sgSub X R.id A' , X≐ p))
solve' (A ≐ tyvar X) _ = do 
  (A' , p) ← check' X A
  just (delete X , (sgSub X R.id A' , ≐X p))
solve' (A ⇒ B ≐ A′ ⇒ B′) (suc n) = do
  (Ξ₁ , σ , p) ← solve' (A ≐ A′ ∙ B ≐ B′) n
  just (Ξ₁ , (σ , (⇒E p)))
solve' (E ∙ F) (suc n) = do 
  (Ξ , σ , p₁) ← solve' E n
  (Ξ₂ , τ , p₂) ← solve' (subEqs σ F) n
  just (Ξ₂ , subSub τ σ , p₁ ∙ p₂)

generate : (Γ : Cxt Ξ n) → (e : Exp n) → Σ[ Ξ₁ ∈ TyCxt ] Σ[ η ∈ (Ξ ⊆ Ξ₁) ] Σ[ A ∈ (Ty Ξ₁) ] Σ[ E ∈ (Eqs Ξ₁) ]  Inf Γ e η A E
generate {Ξ} Γ (var x) = Ξ , R.id , (lookup Γ x , (ε , Inf.var))
generate Γ (abs e) = 
  let 
    (Ξ₁ , η , A , E , e')  = generate (tyvar zero ∷ wkCxt1 Γ) e
  in
    Ξ₁ , (R.wk R.⊙ η , ((wkTy η (tyvar zero) ⇒ A) , (E , Inf.abs e')))
generate Γ (app f e) = 
  let
    (Ξ₁ , η₁ , C , E , f')  = generate Γ f
    (Ξ₂ , η₂ , A , F , e')  = generate (wkCxt η₁ Γ) e
    X = tyvar zero
    η₂′ = η₂ R.⊙ R.wk
  in
    (suc (Ξ₂)) , ((η₁ R.⊙ η₂′) , (X , ((wkEqs η₂′ E ∙ (wkEqs1 F ∙ (wkTy η₂′ C ≐ wkTy1 A ⇒ X))) , app f' e')))


infer : (Γ : Cxt Ξ n) → Exp n → Maybe (∃[ Ξ₂ ] Ty Ξ₂)
infer Γ e = do
  let (Ξ₁ , η , A , E , e')  = generate Γ e
  (Ξ₂ , σ , p) ← solve' E 100000
  just (Ξ₂ , subTy σ A)


id-fun : Exp 0
id-fun = abs (var zero)

id-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
id-tc = infer {zero} [] id-fun

test-id : id-tc ≡ just (suc zero , (tyvar zero) ⇒ (tyvar zero))
test-id = refl

app-fun : Exp 2
app-fun = app (var (suc zero)) (var zero)

app-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
app-tc = infer {2} ((tyvar zero) ∷ (tyvar (suc zero)) ∷ []) app-fun

test-app : app-tc ≡ just (2 , (tyvar zero))
test-app = refl

retlam-fun : Exp 2
retlam-fun = app (var (suc zero)) (var zero)

myVec1 : Vec ℕ 5
myVec1 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

retlam-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
retlam-tc = 
  infer {2} ((tyvar zero) ∷ (tyvar zero ⇒ tyvar (suc zero) ⇒ tyvar (suc zero)) ∷ []) retlam-fun

test-retlam : retlam-tc ≡ just (2 , (tyvar (suc zero) ⇒ tyvar (suc zero)))
test-retlam = refl

app2-fun : Exp 2
app2-fun = (app (var (suc zero)) (app (var (suc zero)) (var zero)))

app2-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
app2-tc = infer {2} ((tyvar zero) ∷ (tyvar (suc zero) ⇒ tyvar (suc zero)) ∷ []) app2-fun

test-app2 : app2-tc ≡ just (1 , (tyvar zero))
test-app2 = refl

lamapp-fun : Exp 1
lamapp-fun = abs (app (var (suc zero)) (app (var (suc zero)) (var zero)))

lamapp-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
lamapp-tc = infer {1} ((tyvar (zero) ⇒ tyvar (zero)) ∷ []) lamapp-fun

test-lamapp : lamapp-tc ≡ just (1 , (tyvar zero ⇒ tyvar zero))
test-lamapp = refl

-- two = ƛ ƛ (# 1 · (# 1 · # 0))
two : Exp 0
two = abs (abs (app (var (suc zero)) (app (var (suc zero)) (var zero))))

two-tc : Maybe (∃[ Ξ₂ ] Ty Ξ₂)
two-tc = infer {zero} [] two

test-two : two-tc ≡ just (1 , ((tyvar zero) ⇒ (tyvar zero)) ⇒ ((tyvar zero) ⇒ (tyvar zero)))
test-two = refl 