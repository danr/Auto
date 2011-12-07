-- Automatic induction for a simple language with +, suc, zero and variables --
module Auto where

open import Data.Vec
open import Data.Nat hiding (pred ; _≟_)
open import Data.Fin hiding (_+_ ; pred)
open import Data.Fin.Props renaming (_≟_ to _≟-Fin_)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Vec.N-ary
open import Data.Maybe
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Function

-- Expressions with n variables -----------------------------------------------
data Expr (n : ℕ) : Set where
  var  : (x : Fin n)      → Expr n
  _⊕_  : (e₁ e₂ : Expr n) → Expr n
  suc  : (e : Expr n)     → Expr n
  zero : Expr n

-- Decidable Equality (in a module to hide some boring functions) -------------
module DecidableEquality where
  private
    -- Boring functions to define decidable equality
    unvar : {n : ℕ} {x y : Fin n} → var x ≡ var y → x ≡ y
    unvar refl      = refl

    left : {n : ℕ} → Expr n → Expr n
    left (e₁ ⊕ e₂)  = e₁
    left _          = zero

    right : {n : ℕ} → Expr n → Expr n
    right (e₁ ⊕ e₂) = e₂
    right _         = zero

    pred : {n : ℕ} → Expr n → Expr n
    pred (suc e)    = e
    pred _          = zero

  -- Decidable equality
  _≟_ : {n : ℕ} → Decidable {A = Expr n} _≡_
  var x     ≟ var y     = map′ (cong var) unvar (x ≟-Fin y)
  var x     ≟ (e₁ ⊕ e₂) = no λ ()
  var x     ≟ suc e     = no λ ()
  var x     ≟ zero      = no λ ()
  (e₁ ⊕ e₂) ≟ var x     = no λ ()
  (e₁ ⊕ e₂) ≟ (e₁′ ⊕ e₂′) with e₁ ≟ e₁′ | e₂ ≟ e₂′
  (e₁ ⊕ e₂) ≟ (.e₁ ⊕ .e₂) | yes refl | yes refl = yes refl
  ...                     | no ¬p    | _        = no (¬p ∘ cong left)
  ...                     | _        | no ¬p    = no (¬p ∘ cong right)
  (e₁ ⊕ e₂) ≟ suc e     = no λ ()
  (e₁ ⊕ e₂) ≟ zero      = no λ ()
  suc e     ≟ var x     = no λ ()
  suc e     ≟ (e₁ ⊕ e₂) = no λ ()
  suc e     ≟ suc e'    = map′ (cong suc) (cong pred) (e ≟ e')
  suc e     ≟ zero      = no λ ()
  zero      ≟ var x     = no λ ()
  zero      ≟ (e₁ ⊕ e₂) = no λ ()
  zero      ≟ suc e     = no λ ()
  zero      ≟ zero      = yes refl

open DecidableEquality

-- The environment datatype ---------------------------------------------------
Env : ℕ → Set
Env n = Vec ℕ n

-- Evaluation of an expression for a given environment ------------------------
⟦_⟧ : ∀ {n} → Expr n → Env n → ℕ
⟦ var x   ⟧ Γ = lookup x Γ
⟦ e₁ ⊕ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ + ⟦ e₂ ⟧ Γ
⟦ suc e   ⟧ Γ = suc (⟦ e ⟧ Γ)
⟦ zero    ⟧ Γ = zero

-- A datatype containing an equality proof under any environment --------------
data Equality {n : ℕ} (lhs rhs : Expr n) : Set where
  equality : (eq : (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
           → Equality lhs rhs

getEquality : {n : ℕ} {lhs rhs : Expr n}
            → Maybe (Equality lhs rhs)
            → (Γ : Env n)
            → Maybe (⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
getEquality nothing              Γ = nothing
getEquality (just (equality eq)) Γ = just (eq Γ)

{-
-- These are unused, but it would be nice to only have rules for this
-- to define normalize
plus-Z : Equality {1} (zero ⊕ var (# 0)) (var (# 0))
plus-Z = equality (λ Γ → refl)

plus-S : Equality {2} (suc (var (# 0)) ⊕ var (# 1))
                      (suc (var (# 0) ⊕ var (# 1)))
plus-S = equality (λ Γ → refl)

rules : List (∃ λ n → ∃₂ (Equality {n}))
rules = (, , , plus-Z) ∷ (, , , plus-S) ∷ []
-}

-- Normalization --------------------------------------------------------------
-- I think I am overcomplicating this. How would one prove completeness?
normalize : {n : ℕ} (e : Expr n) → ∃ λ e′ → ∀ Γ → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ
normalize (var x)       = var x                             , λ _ → refl
normalize (var x ⊕ e₂)  = var x ⊕ (proj₁ (normalize e₂))    , λ Γ → cong (_+_ (lookup x Γ)) (proj₂ (normalize e₂) Γ)
normalize (suc e₁ ⊕ e₂) = suc (proj₁ (normalize (e₁ ⊕ e₂))) , λ Γ → cong suc (proj₂ (normalize (e₁ ⊕ e₂)) Γ)
normalize (zero ⊕ e₂)   = normalize e₂
normalize (suc e)       = suc (proj₁ (normalize e))         , λ Γ → cong suc (proj₂ (normalize e) Γ)
normalize zero          = zero                              , λ _ → refl
normalize ((e₁ ⊕ e₂) ⊕ e₃) with normalize (e₁ ⊕ e₂)
... | e₁' ⊕ e₂' , eq₁₂ = (e₁' ⊕ e₂') ⊕ proj₁ (normalize e₃) , λ Γ → eq₁₂ Γ ⟨ cong₂ _+_ ⟩ proj₂ (normalize e₃) Γ
... | var x     , eq₁₂ = var x ⊕ proj₁ (normalize e₃)       , λ Γ → eq₁₂ Γ ⟨ cong₂ _+_ ⟩ proj₂ (normalize e₃) Γ
... | suc e     , eq₁₂ = suc (e ⊕ proj₁ (normalize e₃))     , λ Γ → eq₁₂ Γ ⟨ cong₂ _+_ ⟩ proj₂ (normalize e₃) Γ
... | zero      , eq₁₂ = proj₁ (normalize e₃)               , λ Γ → eq₁₂ Γ ⟨ cong₂ _+_ ⟩ proj₂ (normalize e₃) Γ

-- Induction instantiation ----------------------------------------------------

-- Base case: replace variable 0 with constant zero
inst-zero : {n : ℕ} → Expr (suc n) → Expr n
inst-zero (var zero)    = zero
inst-zero (var (suc i)) = var i
inst-zero (e₁ ⊕ e₂)     = inst-zero e₁ ⊕ inst-zero e₂
inst-zero (suc e)       = suc (inst-zero e)
inst-zero zero          = zero

-- Induction step: replace variable 0 with suc of the variable
inst-suc : {n : ℕ} → Expr (suc n) → Expr (suc n)
inst-suc (var zero)    = suc (var zero)
inst-suc (var (suc i)) = var (suc i)
inst-suc (e₁ ⊕ e₂)     = inst-suc e₁ ⊕ inst-suc e₂
inst-suc (suc e)       = suc (inst-suc e)
inst-suc zero          = zero

-- Base
inst-zero-eval : {n : ℕ} (e : Expr (suc n)) (Γ : Env n)
               → ⟦ inst-zero e ⟧ Γ ≡ ⟦ e ⟧ (0 ∷ Γ)
inst-zero-eval (var zero)    Γ = refl
inst-zero-eval (var (suc i)) Γ = refl
inst-zero-eval (e₁ ⊕ e₂)     Γ = inst-zero-eval e₁ Γ ⟨ cong₂ _+_ ⟩ inst-zero-eval e₂ Γ
inst-zero-eval (suc e)       Γ = cong suc (inst-zero-eval e Γ)
inst-zero-eval zero          Γ = refl

-- Step
inst-suc-eval : {n : ℕ} (k : ℕ) (e : Expr (suc n)) (Γ : Env n)
              → ⟦ inst-suc e ⟧ (k ∷ Γ) ≡ ⟦ e ⟧ (suc k ∷ Γ)
inst-suc-eval k (var zero)    Γ = refl
inst-suc-eval k (var (suc i)) Γ = refl
inst-suc-eval k (e₁ ⊕ e₂)     Γ = inst-suc-eval k e₁ Γ ⟨ cong₂ _+_ ⟩ inst-suc-eval k e₂ Γ
inst-suc-eval k (suc e)       Γ = cong suc (inst-suc-eval k e Γ)
inst-suc-eval k zero          Γ = refl

-- Induction ------------------------------------------------------------------
induction-inst : {n : ℕ} (lhs rhs : Expr (suc n))
               → (∀ Γ → ⟦ inst-zero lhs ⟧ Γ ≡ ⟦ inst-zero rhs ⟧ Γ)
               → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
                      → ⟦ inst-suc lhs ⟧ Γ ≡ ⟦ inst-suc rhs ⟧ Γ)
               → ∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
induction-inst lhs rhs p0 ps (zero ∷ Γ)  = sym (inst-zero-eval lhs Γ) ⟨ trans ⟩
                                           p0 Γ                       ⟨ trans ⟩
                                           inst-zero-eval rhs Γ
induction-inst lhs rhs p0 ps (suc k ∷ Γ) = sym (inst-suc-eval k lhs Γ)                       ⟨ trans ⟩
                                           ps (k ∷ Γ) (induction-inst lhs rhs p0 ps (k ∷ Γ)) ⟨ trans ⟩
                                           inst-suc-eval k rhs Γ

cong-⟦⟧ : {n : ℕ} {e₁ e₂ : Expr n} (Γ : Env n) → e₁ ≡ e₂ → ⟦ e₁ ⟧ Γ ≡ ⟦ e₂ ⟧ Γ
cong-⟦⟧ Γ = cong (λ e → ⟦ e ⟧ Γ)

-- Instantiate the induction hypothesis. Match the goal with the given. -------
inst-ih : {n : ℕ} (hl hr sl sr : Expr (suc n))
        → Maybe (∀ Γ → ⟦ hl ⟧ Γ ≡ ⟦ hr ⟧ Γ → ⟦ sl ⟧ Γ ≡ ⟦ sr ⟧ Γ)
inst-ih hl hr sl sr with sl ≟ sr | sl ≟ hl | hr ≟ sr
-- The step sides match
... | yes s-eq | _        | _        = just λ Γ _  → cong-⟦⟧ Γ s-eq
-- The step sides match the induction hypothesis
... | _        | yes l-eq | yes r-eq = just λ Γ ih → cong-⟦⟧ Γ l-eq ⟨ trans ⟩ ih ⟨ trans ⟩ cong-⟦⟧ Γ r-eq
-- The step sides both start with suc
inst-ih hl hr (suc sl)  (suc sr)  | _ | _ | _ with inst-ih hl hr sl sr
... | just p  = just λ Γ ih → cong suc (p Γ ih)
... | nothing = nothing
-- The step sides both start with ⊕
inst-ih hl hr (l₁ ⊕ l₂) (r₁ ⊕ r₂) | _ | _ | _ with inst-ih hl hr l₁ r₁ | inst-ih hl hr l₂ r₂
... | just p₁ | just p₂ = just λ Γ ih → p₁ Γ ih ⟨ cong₂ _+_ ⟩ p₂ Γ ih
... | _       | _       = nothing
inst-ih hl hr sl sr               | _ | _ | _ = nothing

-- Induction on the first variable --------------------------------------------
induction : {n : ℕ} (lhs rhs : Expr (suc n)) → Maybe (Equality lhs rhs)
induction lhs rhs with normalize (inst-zero lhs) | normalize (inst-zero rhs)
... | lhs-0 , eq-l-0 | rhs-0 , eq-r-0 with lhs-0 ≟ rhs-0
-- Base case failed
... | no ¬p = nothing
-- Base case suceeded
... | yes p with normalize lhs | normalize rhs | normalize (inst-suc lhs) | normalize (inst-suc rhs)
... | lhs-h , eq-l-h | rhs-h , eq-r-h | lhs-s , eq-l-s | rhs-s , eq-r-s with inst-ih lhs-h rhs-h lhs-s rhs-s
-- Induction step suceeded
... | just ih-normalized = just (equality (induction-inst lhs rhs
                                            (λ Γ → eq-l-0 Γ ⟨ trans ⟩ cong-⟦⟧ Γ p ⟨ trans ⟩ sym (eq-r-0 Γ))
                                            (λ Γ ih → eq-l-s Γ                        ⟨ trans ⟩
                                                      ih-normalized Γ (sym (eq-l-h Γ) ⟨ trans ⟩
                                                                       ih             ⟨ trans ⟩
                                                                       eq-r-h Γ )     ⟨ trans ⟩
                                                      sym (eq-r-s Γ))))
-- Induction step failed
... | nothing = nothing

-- Prove a property -----------------------------------------------------------
prove : {n : ℕ} (lhs rhs : Expr n) → Maybe (Equality lhs rhs)
prove {zero} lhs rhs with normalize lhs | normalize rhs
... | lhs′ , eql | rhs′ , eqr with lhs′ ≟ rhs′
... | yes p = just (equality (λ Γ → eql Γ ⟨ trans ⟩ cong-⟦⟧ Γ p ⟨ trans ⟩ sym (eqr Γ)))
... | no ¬p = nothing
prove {suc n} lhs rhs = induction lhs rhs

-- Some examples --------------------------------------------------------------
assoc-plus-vec : (Γ : Env 3) → lookup (# 0) Γ + (lookup (# 1) Γ + lookup (# 2) Γ)
                             ≡ (lookup (# 0) Γ + lookup (# 1) Γ) + lookup (# 2) Γ
assoc-plus-vec = from-just
               ∘ getEquality (prove (var (# 0) ⊕ (var (# 1) ⊕ var (# 2)))
                                    ((var (# 0) ⊕ (var (# 1))) ⊕ var (# 2)))


assoc-plus : ∀ x y z → x + (y + z) ≡ (x + y) + z
assoc-plus x y z = assoc-plus-vec (x ∷ y ∷ z ∷ [])

move-suc : ∀ x y → suc x + y ≡ x + suc y
move-suc x y = from-just (getEquality (prove (suc (var (# 0)) ⊕ (var (# 1)))
                                             (var (# 0) ⊕ suc (var (# 1))))
                                             (x ∷ y ∷ []))

left-id : ∀ x → x ≡ x + zero
left-id x = from-just (getEquality (prove (var (# 0)) (var (# 0) ⊕ zero)) (x ∷ []))

{-

comm-plus x y = from-just (getEquality (prove (var (# 0) ⊕ var (# 1))
                                              (var (# 1) ⊕ var (# 0)))
                                              (x ∷ y ∷ []))
-}

-- It would be nice to show this automatically
comm-plus : ∀ x y → x + y ≡ y + x
comm-plus zero    y = left-id y
comm-plus (suc x) y = cong suc (comm-plus x y) ⟨ trans ⟩ move-suc y x
