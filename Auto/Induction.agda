open import Auto.Model

module Auto.Induction {T : Theory} (M : Model T) where

open Model M

open import Data.Vec as Vec
open import Data.Fin hiding (_+_)
open import Data.Nat renaming (_≟_ to _≟-Nat_)
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Function

import Auto.ProofDatatypes as PD ; open PD M
import Auto.Normalization  as N  ; open N M
import Auto.Instantiation  as I  ; open I M
import Auto.ReplaceZero    as R  ; open R M

open import Auto.Pretty

private
  -- Induction ------------------------------------------------------------------
  induction-inst : {n : ℕ} (lhs rhs : Expr (suc n))
                 → Equality (inst-zero lhs) (inst-zero rhs)
                 → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
                        → ⟦ inst-suc lhs ⟧ Γ ≡ ⟦ inst-suc rhs ⟧ Γ)
                 → Equality lhs rhs
  induction-inst lhs rhs p0 ps (zero ∷ Γ)  = sym (inst-zero-correct lhs Γ) ⟨ trans ⟩
                                             p0 Γ                          ⟨ trans ⟩
                                             inst-zero-correct rhs Γ
  induction-inst lhs rhs p0 ps (suc k ∷ Γ) = sym (inst-suc-correct k lhs Γ)                    ⟨ trans ⟩
                                             ps (k ∷ Γ) (induction-inst lhs rhs p0 ps (k ∷ Γ)) ⟨ trans ⟩
                                             inst-suc-correct k rhs Γ

  -- If the expressions are equal, then so is evaluating them under the same environment
  cong-⟦─⟧ : {n : ℕ} {e₁ e₂ : Expr n} (Γ : Env n) → e₁ ≡ e₂ → ⟦ e₁ ⟧ Γ ≡ ⟦ e₂ ⟧ Γ
  cong-⟦─⟧ Γ = cong (λ e → ⟦ e ⟧ Γ)

  -- Instantiates the first lemma that matches in the given direction
  inst-lemma : {n : ℕ} → LR → List Lemma → (e : Expr n) → Try (∃ (Equality e))
  inst-lemma     lr []                        e = fail (lemma-failed (pretty e))
  inst-lemma {n} lr (lemma m lhs rhs eq ∷ ls) e with n ≟-Nat m
  ... | no ¬p = inst-lemma lr ls e
  inst-lemma lr    (lemma m lhs rhs eq ∷ ls) e | yes refl with e ≟ lhs | e ≟ rhs
  inst-lemma left  (lemma m lhs rhs eq ∷ ls) e | yes refl | yes p | _ = success (lemmaStep (pretty rhs)) (rhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ eq Γ)
  inst-lemma right (lemma m lhs rhs eq ∷ ls) e | yes refl | _ | yes p = success (lemmaStep (pretty lhs)) (lhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ sym (eq Γ))
  ... | _ | _ = inst-lemma lr ls e

  -- Instantiate the induction hypothesis. Match the goal with the given. -------
  induction-step : {n : ℕ}
          → ℕ → List Lemma
          → (hl hr sl sr : Expr (suc n))
          → Try (∀ Γ → ⟦ hl ⟧ Γ ≡ ⟦ hr ⟧ Γ → ⟦ sl ⟧ Γ ≡ ⟦ sr ⟧ Γ)
  induction-step uses lemmas hl hr sl sr with sl ≟ sr | sl ≟ hl | hr ≟ sr
  -- The step sides match
  ... | yes s-eq | _        | _        = success stepSideMatch λ Γ _  → cong-⟦─⟧ Γ s-eq
  -- The step sides match the induction hypothesis
  ... | _        | yes l-eq | yes r-eq = success stepMatchIH λ Γ ih → cong-⟦─⟧ Γ l-eq ⟨ trans ⟩ ih ⟨ trans ⟩ cong-⟦─⟧ Γ r-eq

  {-
  -- The left step side match the induction hypothesis  (this could be nice to use)
  ... | _        | yes l-eq | no ¬p    = ...
  -- The right step side match the induction hypothesis (this could be nice to use)
  ... | _        | no ¬p    | yes r-eq = ...
  -}

  -- The step sides both start with suc
  induction-step uses lemmas hl hr (suc sl)  (suc sr)  | _ | _ | _ with induction-step uses lemmas hl hr sl sr
  ... | success t p = success (stepSuc t) λ Γ ih → cong suc (p Γ ih)
  ... | fail e      = fail e

  -- Add this for unary and binary operators :D
  -- The step sides both start with ⊕
  -- induction-step uses lemmas hl hr (l₁ ⊕ l₂) (r₁ ⊕ r₂) | _ | _ | _ with induction-step uses lemmas hl hr l₁ r₁ | induction-step uses lemmas hl hr l₂ r₂
  -- ... | success t₁ p₁ | success t₂ p₂ = success (t₁ stepPlus t₂) λ Γ ih → p₁ Γ ih ⟨ cong₂ _+_ ⟩ p₂ Γ ih
  -- ... | _             | _             = fail (step-failed (pretty hl) (pretty hr) pretty .. (l₁ ⊕ l₂) (r₁ ⊕ r₂))

  -- No lemmas uses left
  induction-step zero         lemmas hl hr sl sr | _ | _ | _ = fail (no-lemmas-left (step-failed (pretty hl) (pretty hr) (pretty sl) (pretty sr)))
  -- Instantiate a lemma
  induction-step (suc uses-1) lemmas hl hr sl sr | _ | _ | _ with inst-lemma left lemmas sl | inst-lemma right lemmas sr
  ... | success t (sl′ , sl≡sl′) | _ = (λ ih' Γ ih → sl≡sl′ Γ ⟨ trans ⟩ ih' Γ ih)
                                  <$>⟨ apply t ⟩ induction-step uses-1 lemmas hl hr sl′ sr
  ... | _ | success t (sr′ , sr≡sr′) = (λ ih' Γ ih → ih' Γ ih ⟨ trans ⟩ sym (sr≡sr′ Γ))
                                  <$>⟨ apply t ⟩ induction-step uses-1 lemmas hl hr sl sr′
  ... | _ | _ = fail (step-failed (pretty hl) (pretty hr) (pretty sl) (pretty sr))

  -- Simplifylification. ------------------------------------------------------------
  -- Used for the base case and for proving equality with no variables
  simplify : {n : ℕ}
       → ℕ → List Lemma
       → (lhs rhs : Expr n)
       -- ^ normalized lhs and rhs
       → Try (Equality lhs rhs)
  simplify uses lemmas lhs rhs with lhs ≟ rhs
  -- lhs ≡ rhs by reflexivity
  ... | yes p = success refl (λ Γ → cong-⟦─⟧ Γ p)
  -- No lemma uses left
  simplify zero         lemmas lhs rhs | no ¬p = fail (no-lemmas-left (simplify-failed (pretty lhs) (pretty rhs)))
  -- Try to use a lemma
  simplify (suc uses-1) lemmas lhs rhs | no ¬p with inst-lemma left lemmas lhs | inst-lemma right lemmas rhs
  ... | success t (lhs′ , lhs≡lhs′) | _ = (λ x Γ → lhs≡lhs′ Γ ⟨ trans ⟩ x Γ)
                                        <$>⟨ apply t ⟩ simplify uses-1 lemmas lhs′ rhs
  ... | _ | success t (rhs′ , rhs≡rhs′) = (λ x Γ → x Γ ⟨ trans ⟩ sym (rhs≡rhs′ Γ))
                                        <$>⟨ apply t ⟩ simplify uses-1 lemmas lhs rhs′
  ... | _ | _ = fail (simplify-failed (pretty lhs) (pretty rhs))

  -- Induction on the first variable --------------------------------------------
  induction : {n : ℕ}
            → ℕ → List Lemma
            → (lhs rhs : Expr (suc n)) → Try (Equality lhs rhs)
  induction uses lemmas lhs rhs with simplify uses lemmas (normalize (inst-zero lhs))
                                                      (normalize (inst-zero rhs))
  -- Base case failed
  ... | fail e = fail (base-failed e)
  -- Base case suceeded
  ... | success tb base with induction-step uses lemmas (normalize lhs) (normalize rhs)
                                                 (normalize (inst-suc lhs))
                                                 (normalize (inst-suc rhs))
  -- Induction step suceeded
  ... | success th ih-norm = success base⟨ tb ⟩step⟨ th ⟩
                                (induction-inst lhs rhs
                                   (λ Γ → normalize-correct (inst-zero lhs) Γ         ⟨ trans ⟩
                                          base Γ                                      ⟨ trans ⟩
                                          sym (normalize-correct (inst-zero rhs) Γ))
                                   (λ Γ ih → normalize-correct (inst-suc lhs) Γ       ⟨ trans ⟩
                                             ih-norm Γ (sym (normalize-correct lhs Γ) ⟨ trans ⟩
                                                       ih                             ⟨ trans ⟩
                                                       normalize-correct rhs Γ )      ⟨ trans ⟩
                                             sym (normalize-correct (inst-suc rhs) Γ)))
  -- Induction step failed
  ... | fail e = fail e

-- Prove a property with lemmas -----------------------------------------------
prove-with-lemmas : (n : ℕ) (lhs rhs : Expr n)
                  → ℕ → List Lemma
                  → Try (Equality lhs rhs)
prove-with-lemmas (suc n) lhs rhs u lemmas = induction u lemmas lhs rhs
prove-with-lemmas zero    lhs rhs u lemmas = (λ x Γ → normalize-correct lhs Γ ⟨ trans ⟩
                                                      x Γ                     ⟨ trans ⟩
                                                      sym (normalize-correct rhs Γ))
                                            <$>⟨ id ⟩ simplify u lemmas (normalize lhs) (normalize rhs)


-- Prove a property without lemmas --------------------------------------------
prove : (n : ℕ) (lhs rhs : Expr n) → Try (Equality lhs rhs)
prove n lhs rhs = prove-with-lemmas n lhs rhs 1 []

prove-with-induction-on-and-lemmas : (n : ℕ) (v : Fin n) (lhs rhs : Expr n)
                                   → ℕ → List Lemma
                                   → Try (Equality lhs rhs)
prove-with-induction-on-and-lemmas zero    () lhs rhs u lemmas
prove-with-induction-on-and-lemmas (suc n) v  lhs rhs u lemmas =
   reshuffle-correct lhs rhs v <$>⟨ reshuffle ⟩
   prove-with-lemmas (suc n) (place v first lhs) (place v first rhs) u lemmas

prove-with-induction-on : (n : ℕ) (v : Fin n) (lhs rhs : Expr n)
                        → Try (Equality lhs rhs)
prove-with-induction-on n v lhs rhs = prove-with-induction-on-and-lemmas n v lhs rhs 1 []

open import Data.Vec.N-ary
open import Function.Equivalence using (module Equivalence)
open import Function.Equality using (_⟨$⟩_)

close : ∀ {A : Set} n → N-ary n (Expr n) A → A
close n f = f $ⁿ Vec.map var (allFin n)

prove′ : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
         Try (∀ⁿ n (curryⁿ λ Γ → ⟦ proj₁ (close n f) ⟧ Γ ≡ ⟦ proj₂ (close n f) ⟧ Γ))
prove′ n f with prove n (proj₁ (close n f)) (proj₂ (close n f))
... | success t r = success t (Equivalence.from (uncurry-∀ⁿ n) ⟨$⟩
                              (λ Γ → subst id
                                           (sym (left-inverse
                                              (λ Γ′ → ⟦ proj₁ (close n f) ⟧ Γ′ ≡
                                                      ⟦ proj₂ (close n f) ⟧ Γ′) Γ))
                                           (r Γ)))
... | fail e      = fail e

prove-with-lemmas′ : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n))
                   → ℕ → List Lemma
                   → Try (∀ⁿ n (curryⁿ λ Γ → ⟦ proj₁ (close n f) ⟧ Γ ≡ ⟦ proj₂ (close n f) ⟧ Γ))
prove-with-lemmas′ n f u lemmas with prove-with-lemmas n (proj₁ (close n f)) (proj₂ (close n f)) u lemmas
... | success t r = success t (Equivalence.from (uncurry-∀ⁿ n) ⟨$⟩
                              (λ Γ → subst id
                                           (sym (left-inverse
                                              (λ Γ′ → ⟦ proj₁ (close n f) ⟧ Γ′ ≡
                                                      ⟦ proj₂ (close n f) ⟧ Γ′) Γ))
                                           (r Γ)))
... | fail e      = fail e

infix 4 _==_

_==_ : ∀ {n} → Expr n → Expr n → Expr n × Expr n
_==_ = _,_

lemma′ : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
         Try Lemma
lemma′ n f with prove n (proj₁ (close n f)) (proj₂ (close n f))
... | success t r = success t (lemma n (proj₁ (close n f)) (proj₂ (close n f)) r)
... | fail e      = fail e