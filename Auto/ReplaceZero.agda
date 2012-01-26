open import Auto.Model

module Auto.ReplaceZero {T : Theory} (M : Model T) where

open Model M

open import Data.Vec hiding ([_])
open import Data.Nat renaming (pred to Nat-pred ; _≟_ to _≟-Nat_)
open import Data.Fin hiding (_+_ ; pred)
open import Data.Fin.Props renaming (_≟_ to _≟-Fin_)
open import Data.Product
open import Data.Empty

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary

open import Function

import Auto.ProofDatatypes as PD; open PD M

place_first : ∀ {n} → Fin (suc n) → Expr (suc n) → Expr (suc n)
place i first (var x) with x ≟-Fin zero | i ≟-Fin x
... | yes p | _      = var i
... | no ¬p | yes p  = var zero
... | no ¬p | no ¬p′ = var x
place i first (e₁ ⟪ b ⟫ e₂) = place i first e₁ ⟪ b ⟫ place i first e₂
place i first (u ∙ e)       = u ∙ (place i first e)
place i first (suc e)       = suc (place i first e)
place i first zero          = zero

private
  []-lookup : {A : Set} {n : ℕ} (i : Fin n) (xs : Vec A n) (v : A)
            → lookup i (xs [ i ]≔ v) ≡ v
  []-lookup ()      []       x
  []-lookup zero    (x ∷ xs) v = refl
  []-lookup (suc i) (x ∷ xs) v = []-lookup i xs v

  lemma₁ : {A : Set} {n : ℕ} (i : Fin (suc n)) (Γ : Vec A (suc n))
         → lookup i Γ ≡ lookup zero (Γ [ zero ]≔ lookup i Γ [ i ]≔ lookup zero Γ)
  lemma₁ zero    (x ∷ xs) = refl
  lemma₁ (suc i) (x ∷ xs) = refl

  lemma₂ : {A : Set} {n : ℕ} (i : Fin (suc n)) (Γ : Vec A (suc n))
         → lookup zero Γ ≡ lookup i (Γ [ zero ]≔ lookup i Γ [ i ]≔ lookup zero Γ)
  lemma₂ zero    (x ∷ xs) = refl
  lemma₂ (suc i) (x ∷ xs) = sym ([]-lookup i xs x)

  lemma³ : {A : Set} {n : ℕ} (i x : Fin n) (γ : A) (Γ : Vec A n)
         → i ≢ x → lookup x Γ ≡ lookup x (Γ [ i ]≔ γ)
  lemma³ zero    zero    γ Γ i≢x = ⊥-elim (i≢x refl)
  lemma³ zero (suc x)    γ (_ ∷ Γ) i≢x = refl
  lemma³ (suc i) zero    γ (_ ∷ Γ) i≢x = refl
  lemma³ (suc i) (suc x) γ (_ ∷ Γ) i≢x = lemma³ i x γ Γ (i≢x ∘ cong suc)

  lemma₃ : {A : Set} {n : ℕ} (i x : Fin (suc n)) (Γ : Vec A (suc n))
         → x ≢ zero → i ≢ x
         → lookup x Γ ≡ lookup x (Γ [ zero ]≔ lookup i Γ [ i ]≔ lookup zero Γ)
  lemma₃ i       zero    Γ       x≢0 i≢x = ⊥-elim (x≢0 refl)
  lemma₃ zero    (suc x) (γ ∷ Γ) x≢0 i≢x = refl
  lemma₃ (suc i) (suc x) (γ ∷ Γ) x≢0 i≢x = lemma³ i x γ Γ (i≢x ∘ cong suc)

  place-correct : ∀ {n} (i : Fin (suc n)) (e : Expr (suc n))
                → ∀ Γ → ⟦ e ⟧ Γ ≡ ⟦ place i first e ⟧ (Γ [ zero ]≔ lookup i Γ [ i ]≔ lookup zero Γ)
  place-correct i (var x)       Γ with x ≟-Fin zero | i ≟-Fin x
  place-correct i (var .zero)   Γ | yes refl | _        = lemma₂ i Γ
  place-correct i (var .i)      Γ | no ¬p    | yes refl = lemma₁ i Γ
  place-correct i (var x)       Γ | no ¬p    | no ¬p′   = lemma₃ i x Γ ¬p ¬p′
  place-correct i (e₁ ⟪ b ⟫ e₂) Γ = place-correct i e₁ Γ ⟨ cong₂ (Bin-eval b) ⟩ place-correct i e₂ Γ
  place-correct i (op ∙ e)      Γ = cong (Op-eval op) (place-correct i e Γ)
  place-correct i (suc e)       Γ = cong suc (place-correct i e Γ)
  place-correct i zero          Γ = refl

reshuffle-correct : {n : ℕ} (lhs rhs : Expr (suc n)) (v : Fin (suc n))
                  → Equality (place v first lhs) (place v first rhs)
                  → Equality lhs rhs
reshuffle-correct lhs rhs v p Γ = place-correct v lhs Γ                           ⟨ trans ⟩
                                  p (Γ [ zero ]≔ lookup v Γ [ v ]≔ lookup zero Γ) ⟨ trans ⟩
                                  sym (place-correct v rhs Γ)