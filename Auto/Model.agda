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
    bin-normalize         : Bin → {n : ℕ} → Expr n → Expr n → Expr n
    bin-normalize-correct : {n : ℕ} (b : Bin) (e₁ e₂ : Expr n) (Γ : Env n)
                          → ⟦ e₁ ⟪ b ⟫ e₂ ⟧ Γ ≡ ⟦ bin-normalize b e₁ e₂ ⟧ Γ

    op-normalize         : Op → {n : ℕ} → Expr n → Expr n
    op-normalize-correct : {n : ℕ} (op : Op) (e : Expr n) (Γ : Env n)
                         → ⟦ op ∙ e ⟧ Γ ≡ ⟦ op-normalize op e ⟧ Γ

  open E T public
  open Theory T public

