module Auto.Model where

open import Auto.Theory public
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function

import Auto.Expr as E

record Model (T : Theory) : Set₁ where
  open E T
  open Theory T
  field
    bin-normalize         : B → {n : ℕ} → Expr n → Expr n → Expr n
    bin-normalize-correct : {n : ℕ} (b : B) (e₁ e₂ : Expr n) (Γ : Env n)
                          → ⟦ e₁ [ b ] e₂ ⟧ Γ ≡ ⟦ bin-normalize b e₁ e₂ ⟧ Γ

    un-normalize         : U → {n : ℕ} → Expr n → Expr n
    un-normalize-correct : {n : ℕ} (u : U) (e : Expr n) (Γ : Env n)
                          → ⟦ u ∙ e ⟧ Γ ≡ ⟦ un-normalize u e ⟧ Γ

  open E T public
  open Theory T public

