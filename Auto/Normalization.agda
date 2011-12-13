open import Auto.Model

module Auto.Normalization {T : Theory} (M : Model T) where

open Model M

open import Data.Vec
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

-- Normalization of an expression ---------------------------------------------
-- How would one prove completeness?
normalize : {n : ℕ} (e : Expr n) → Expr n
normalize zero          = zero
normalize (suc e)       = suc (normalize e)
normalize (var x)       = var x
normalize (e₁ [ b ] e₂) = bin-normalize b (normalize e₁) (normalize e₂)
normalize (o ∙ e)       = op-normalize o (normalize e)

normalize-correct : {n : ℕ} (e : Expr n) (Γ : Env n)
                  → ⟦ e ⟧ Γ ≡ ⟦ normalize e ⟧ Γ
normalize-correct zero          Γ = refl
normalize-correct (suc e)       Γ = cong suc (normalize-correct e Γ)
normalize-correct (var x)       Γ = refl
normalize-correct (e₁ [ b ] e₂) Γ = normalize-correct e₁ Γ ⟨ cong₂ (Bin-eval b) ⟩ normalize-correct e₂ Γ ⟨ trans ⟩
                                    bin-normalize-correct b (normalize e₁) (normalize e₂) Γ
normalize-correct (op ∙ e)       Γ = cong (Op-eval op) (normalize-correct e Γ) ⟨ trans ⟩
                                    op-normalize-correct op (normalize e) Γ

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

