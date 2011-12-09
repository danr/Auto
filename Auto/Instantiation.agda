module Auto.Instantiation where

open import Data.Vec
open import Data.Fin hiding (_+_)
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

open import Auto.Expr
open import Auto.Normalization

-- Induction instantiation ----------------------------------------------------

-- Replace variable 0 with constant zero
inst-zero : {n : ℕ} → Expr (suc n) → Expr n
inst-zero (var zero)    = zero
inst-zero (var (suc i)) = var i
inst-zero (e₁ ⊕ e₂)     = inst-zero e₁ ⊕ inst-zero e₂
inst-zero (suc e)       = suc (inst-zero e)
inst-zero zero          = zero

-- This operation preserves equality under evaluation
inst-zero-correct : {n : ℕ} (e : Expr (suc n)) (Γ : Env n)
               → ⟦ inst-zero e ⟧ Γ ≡ ⟦ e ⟧ (0 ∷ Γ)
inst-zero-correct (var zero)    Γ = refl
inst-zero-correct (var (suc i)) Γ = refl
inst-zero-correct (e₁ ⊕ e₂)     Γ = inst-zero-correct e₁ Γ ⟨ cong₂ _+_ ⟩ inst-zero-correct e₂ Γ
inst-zero-correct (suc e)       Γ = cong suc (inst-zero-correct e Γ)
inst-zero-correct zero          Γ = refl

-- Replace variable 0 with suc of the variable
inst-suc : {n : ℕ} → Expr (suc n) → Expr (suc n)
inst-suc (var zero)    = suc (var zero)
inst-suc (var (suc i)) = var (suc i)
inst-suc (e₁ ⊕ e₂)     = inst-suc e₁ ⊕ inst-suc e₂
inst-suc (suc e)       = suc (inst-suc e)
inst-suc zero          = zero

-- This operation preserves equality under evaluation
inst-suc-correct : {n : ℕ} (k : ℕ) (e : Expr (suc n)) (Γ : Env n)
              → ⟦ inst-suc e ⟧ (k ∷ Γ) ≡ ⟦ e ⟧ (suc k ∷ Γ)
inst-suc-correct k (var zero)    Γ = refl
inst-suc-correct k (var (suc i)) Γ = refl
inst-suc-correct k (e₁ ⊕ e₂)     Γ = inst-suc-correct k e₁ Γ ⟨ cong₂ _+_ ⟩ inst-suc-correct k e₂ Γ
inst-suc-correct k (suc e)       Γ = cong suc (inst-suc-correct k e Γ)
inst-suc-correct k zero          Γ = refl

