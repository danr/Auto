module Auto.Normalization where

open import Data.Vec
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Auto.Expr

-- Normalization of plus ------------------------------------------------------
_⨁_ : {n : ℕ} → Expr n → Expr n → Expr n
-- Definition of plus
suc e     ⨁ e₂ = suc (e ⨁ e₂)
zero      ⨁ e₂ = e₂
-- Nothing special here
var x     ⨁ e₂ = var x ⊕ e₂
(e₁ ⊕ e₂) ⨁ e₃ = (e₁ ⊕ e₂) ⊕ e₃

⨁-correct : {n : ℕ} (e₁ e₂ : Expr n) (Γ : Env n)
           → ⟦ e₁ ⊕ e₂ ⟧ Γ ≡ ⟦ e₁ ⨁ e₂ ⟧ Γ
⨁-correct (suc e)   e₂ Γ = cong suc (⨁-correct e e₂ Γ)
⨁-correct zero      e₂ Γ = refl
⨁-correct (var x)   e₂ Γ = refl
⨁-correct (e₁ ⊕ e₂) e₃ Γ = refl

-- Normalization of an expression ---------------------------------------------
-- How would one prove completeness?
normalize : {n : ℕ} (e : Expr n) → Expr n
normalize (var x)   = var x
normalize (e₁ ⊕ e₂) = normalize e₁ ⨁ normalize e₂
normalize (suc e)   = suc (normalize e)
normalize zero      = zero

normalize-correct : {n : ℕ} (e : Expr n) (Γ : Env n)
                  → ⟦ e ⟧ Γ ≡ ⟦ normalize e ⟧ Γ
normalize-correct (var x)   Γ = refl
normalize-correct (e₁ ⊕ e₂) Γ = normalize-correct e₁ Γ ⟨ cong₂ _+_ ⟩ normalize-correct e₂ Γ ⟨ trans ⟩
                                ⨁-correct (normalize e₁) (normalize e₂) Γ
normalize-correct (suc e)   Γ = cong suc (normalize-correct e Γ)
normalize-correct zero      Γ = refl

normalize-with-correct : {n : ℕ} (e : Expr n) → ∃ λ e′ → ∀ Γ → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ
normalize-with-correct e = normalize e , normalize-correct e

{-
-- A little failed attempt to show completeness.
-- It should be complete wrt Agda's normalization, but I am not sure
-- how to capture this in a type.

lookup-replicate : {n : ℕ} (x : Fin n) (v : ℕ)
                 → v ≡ lookup x (replicate v)
lookup-replicate zero    v = refl
lookup-replicate (suc i) v = lookup-replicate i v

normalize-complete : {n : ℕ} (e : Expr n) (e′ : Expr n)
                   → ((Γ : Env n) → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ)
                   → normalize e ≡ normalize e′
normalize-complete (var x) (var y  ⊕ zero) eq with x ≟-Fin y
normalize-complete (var x) (var .x ⊕ zero) eq | yes refl = {!!}
-- ^ this is why it is not complete in this sense
--   Goal: var x ≡ var x ⊕ zero
normalize-complete (var x) (var y  ⊕ zero) eq | no ¬p = {!!}
normalize-complete e e′ eq = {!!}
-}

