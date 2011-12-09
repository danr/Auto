module Auto.Induction where

open import Data.Vec
open import Data.Fin hiding (_+_)
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Product
open import Data.List
open import Data.Maybe renaming (functor to maybe-functor)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Function

open import Auto.Expr
open import Auto.Normalization
open import Auto.Instantiation

open import Category.Functor
import Level

open RawFunctor (maybe-functor {Level.zero})

-- Equality proof of two expressions under any environment --------------------
Equality : {n : ℕ} (lhs rhs : Expr n) → Set
Equality {n} lhs rhs = (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ

-- Induction ------------------------------------------------------------------
induction-inst : {n : ℕ} (lhs rhs : Expr (suc n))
               → (∀ Γ → ⟦ inst-zero lhs ⟧ Γ ≡ ⟦ inst-zero rhs ⟧ Γ)
               → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
                      → ⟦ inst-suc lhs ⟧ Γ ≡ ⟦ inst-suc rhs ⟧ Γ)
               → Equality lhs rhs
induction-inst lhs rhs p0 ps (zero ∷ Γ)  = sym (inst-zero-correct lhs Γ) ⟨ trans ⟩
                                           p0 Γ                       ⟨ trans ⟩
                                           inst-zero-correct rhs Γ
induction-inst lhs rhs p0 ps (suc k ∷ Γ) = sym (inst-suc-correct k lhs Γ)                       ⟨ trans ⟩
                                           ps (k ∷ Γ) (induction-inst lhs rhs p0 ps (k ∷ Γ)) ⟨ trans ⟩
                                           inst-suc-correct k rhs Γ

-- If the expressions are equal, then so is evaluating them under the same environment
cong-⟦─⟧ : {n : ℕ} {e₁ e₂ : Expr n} (Γ : Env n) → e₁ ≡ e₂ → ⟦ e₁ ⟧ Γ ≡ ⟦ e₂ ⟧ Γ
cong-⟦─⟧ Γ = cong (λ e → ⟦ e ⟧ Γ)

-- Lemmas ---------------------------------------------------------------------
-- Lemma datatype
data Lemma : Set where
  lemma : (n : ℕ) (lhs rhs : Expr n) (eq : Equality lhs rhs) → Lemma

-- Instantiate direction datatype
data LR : Set where
  left right : LR

-- Instantiates the first lemma that matches in the given direction
inst-lemma : {n : ℕ} → LR → List Lemma → (e : Expr n) → Maybe (∃ (Equality e))
inst-lemma     lr []                       e = nothing
inst-lemma {n} lr (lemma m lhs rhs eq ∷ ls) e with n ≟-Nat m
... | no ¬p = inst-lemma lr ls e
inst-lemma lr    (lemma m lhs rhs eq ∷ ls) e | yes refl with e ≟ lhs | e ≟ rhs
inst-lemma left  (lemma m lhs rhs eq ∷ ls) e | yes refl | yes p | _ = just (rhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ eq Γ)
inst-lemma right (lemma m lhs rhs eq ∷ ls) e | yes refl | _ | yes p = just (lhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ sym (eq Γ))
... | _ | _ = inst-lemma lr ls e

-- Instantiate the induction hypothesis. Match the goal with the given. -------
inst-ih : {n : ℕ}
        → ℕ → List Lemma
        → (hl hr sl sr : Expr (suc n))
        → Maybe (∀ Γ → ⟦ hl ⟧ Γ ≡ ⟦ hr ⟧ Γ → ⟦ sl ⟧ Γ ≡ ⟦ sr ⟧ Γ)
inst-ih uses lemmas hl hr sl sr with sl ≟ sr | sl ≟ hl | hr ≟ sr
-- The step sides match
... | yes s-eq | _        | _        = just λ Γ _  → cong-⟦─⟧ Γ s-eq
-- The step sides match the induction hypothesis
... | _        | yes l-eq | yes r-eq = just λ Γ ih → cong-⟦─⟧ Γ l-eq ⟨ trans ⟩ ih ⟨ trans ⟩ cong-⟦─⟧ Γ r-eq
{-
-- The left step side match the induction hypothesis  (this could be nice to use)
... | _        | yes l-eq | no ¬p    = ...
-- The right step side match the induction hypothesis (this could be nice to use)
... | _        | no ¬p    | yes r-eq = ...
-}
-- The step sides both start with suc
inst-ih uses lemmas hl hr (suc sl)  (suc sr)  | _ | _ | _ with inst-ih uses lemmas hl hr sl sr
... | just p  = just λ Γ ih → cong suc (p Γ ih)
... | nothing = nothing
-- The step sides both start with ⊕
inst-ih uses lemmas hl hr (l₁ ⊕ l₂) (r₁ ⊕ r₂) | _ | _ | _ with inst-ih uses lemmas hl hr l₁ r₁ | inst-ih uses lemmas hl hr l₂ r₂
... | just p₁ | just p₂ = just λ Γ ih → p₁ Γ ih ⟨ cong₂ _+_ ⟩ p₂ Γ ih
... | _       | _       = nothing
-- No lemmas uses left
inst-ih zero         lemmas hl hr sl sr | _ | _ | _ = nothing
-- Instantiate a lemma
inst-ih (suc uses-1) lemmas hl hr sl sr | _ | _ | _ with inst-lemma left lemmas sl | inst-lemma right lemmas sr
... | just (sl′ , sl≡sl′) | _ = (λ ih' Γ ih → sl≡sl′ Γ ⟨ trans ⟩ ih' Γ ih)
                                <$> inst-ih uses-1 lemmas hl hr sl′ sr
... | _ | just (sr′ , sr≡sr′) = (λ ih' Γ ih → ih' Γ ih ⟨ trans ⟩ sym (sr≡sr′ Γ))
                                <$> inst-ih uses-1 lemmas hl hr sl sr′
... | _ | _ = nothing

-- Simplification. ------------------------------------------------------------
-- Used for the base case and for proving equality with no variables
simp : {n : ℕ}
     → ℕ → List Lemma
     → (lhs rhs : Expr n)
     -- ^ normalized lhs and rhs
     → Maybe (Equality lhs rhs)
simp uses lemmas lhs rhs with lhs ≟ rhs
-- lhs ≡ rhs by reflexivity
... | yes p = just (λ Γ → cong-⟦─⟧ Γ p)
-- No lemma uses left
simp zero         lemmas lhs rhs | no ¬p = nothing
-- Try to use a lemma
simp (suc uses-1) lemmas lhs rhs | no ¬p with inst-lemma left lemmas lhs | inst-lemma right lemmas rhs
... | just (lhs′ , lhs≡lhs′) | _ = (λ x Γ → lhs≡lhs′ Γ ⟨ trans ⟩ x Γ) <$> simp uses-1 lemmas lhs′ rhs
... | _ | just (rhs′ , rhs≡rhs′) = (λ x Γ → x Γ ⟨ trans ⟩ sym (rhs≡rhs′ Γ)) <$> simp uses-1 lemmas lhs rhs′
... | _ | _ = nothing

-- Induction on the first variable --------------------------------------------
induction : {n : ℕ}
          → ℕ → List Lemma
          → (lhs rhs : Expr (suc n)) → Maybe (Equality lhs rhs)
induction uses lemmas lhs rhs with normalize-with-correct (inst-zero lhs) | normalize-with-correct (inst-zero rhs)
... | lhs-0 , eq-l-0 | rhs-0 , eq-r-0 with simp uses lemmas lhs-0 rhs-0
-- Base case failed
... | nothing = nothing
-- Base case suceeded
... | just base with normalize-with-correct lhs | normalize-with-correct rhs | normalize-with-correct (inst-suc lhs) | normalize-with-correct (inst-suc rhs)
... | lhs-h , eq-l-h | rhs-h , eq-r-h | lhs-s , eq-l-s | rhs-s , eq-r-s with inst-ih uses lemmas lhs-h rhs-h lhs-s rhs-s
-- Induction step suceeded
... | just ih-normalized = just (induction-inst lhs rhs
                                    (λ Γ → eq-l-0 Γ ⟨ trans ⟩ base Γ ⟨ trans ⟩ sym (eq-r-0 Γ))
                                    (λ Γ ih → eq-l-s Γ                        ⟨ trans ⟩
                                              ih-normalized Γ (sym (eq-l-h Γ) ⟨ trans ⟩
                                                               ih             ⟨ trans ⟩
                                                               eq-r-h Γ )     ⟨ trans ⟩
                                              sym (eq-r-s Γ)))
-- Induction step failed
... | nothing = nothing

-- Prove a property with lemmas -----------------------------------------------
prove-with-lemmas : ℕ → List Lemma → (n : ℕ) (lhs rhs : Expr n) → Maybe (Equality lhs rhs)
prove-with-lemmas u lemmas (suc n) lhs rhs = induction u lemmas lhs rhs
prove-with-lemmas u lemmas zero    lhs rhs with normalize-with-correct lhs | normalize-with-correct rhs
... | lhs′ , eql | rhs′ , eqr = (λ x Γ → eql Γ ⟨ trans ⟩ x Γ ⟨ trans ⟩ sym (eqr Γ))
                                <$> simp u lemmas lhs′ rhs′


-- Prove a property without lemmas --------------------------------------------
prove : (n : ℕ) (lhs rhs : Expr n) → Maybe (Equality lhs rhs)
prove = prove-with-lemmas 0 []

