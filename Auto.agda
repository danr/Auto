module Auto where

open import Data.Vec
open import Data.Nat hiding (pred)
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

Env : ℕ → Set
Env n = Vec ℕ n

data Expr (n : ℕ) : Set where
  var  : (x : Fin n) → Expr n
  _⊕_ : (e₁ e₂ : Expr n) → Expr n
  suc  : (e : Expr n) → Expr n
  zero : Expr n

inst-zero : {n : ℕ} → Expr (suc n) → Expr n
inst-zero (var zero)    = zero
inst-zero (var (suc i)) = var i
inst-zero (e₁ ⊕ e₂)     = inst-zero e₁ ⊕ inst-zero e₂
inst-zero (suc e)       = suc (inst-zero e)
inst-zero zero          = zero

inst-suc : {n : ℕ} → Expr (suc n) → Expr (suc n)
inst-suc (var zero)    = suc (var zero)
inst-suc (var (suc i)) = var (suc i)
inst-suc (e₁ ⊕ e₂)     = inst-suc e₁ ⊕ inst-suc e₂
inst-suc (suc e)       = suc (inst-suc e)
inst-suc zero          = zero

unvar : {n : ℕ} {x y : Fin n} → var x ≡ var y → x ≡ y
unvar refl = refl

left : {n : ℕ} → Expr n → Expr n
left (e₁ ⊕ e₂) = e₁
left _ = zero

right : {n : ℕ} → Expr n → Expr n
right (e₁ ⊕ e₂) = e₂
right _ = zero

pred : {n : ℕ} → Expr n → Expr n
pred (suc e) = e
pred _ = zero

_≟-Expr_ : {n : ℕ} → Decidable {A = Expr n} _≡_
var x ≟-Expr var y = map′ (cong var) unvar (x ≟-Fin y)
var x ≟-Expr (e₁ ⊕ e₂) = no (λ ())
var x ≟-Expr suc e = no (λ ())
var x ≟-Expr zero = no (λ ())
(e₁ ⊕ e₂) ≟-Expr var x = no (λ ())
(e₁ ⊕ e₂) ≟-Expr (e₁' ⊕ e₂') with e₁ ≟-Expr e₁' | e₂ ≟-Expr e₂'
(.e₁' ⊕ .e₂') ≟-Expr (e₁' ⊕ e₂') | yes refl | yes refl = yes refl
... | no ¬p | _ = no (¬p ∘ cong left)
... | _ | no ¬p = no (¬p ∘ cong right)
(e₁ ⊕ e₂) ≟-Expr suc e = no (λ ())
(e₁ ⊕ e₂) ≟-Expr zero = no (λ ())
suc e ≟-Expr var x = no (λ ())
suc e ≟-Expr (e₁ ⊕ e₂) = no (λ ())
suc e ≟-Expr suc e' = map′ (cong suc) (cong pred) (e ≟-Expr e')
suc e ≟-Expr zero = no (λ ())
zero ≟-Expr var x = no (λ ())
zero ≟-Expr (e₁ ⊕ e₂) = no (λ ())
zero ≟-Expr suc e = no (λ ())
zero ≟-Expr zero = yes refl

⟦_⟧ : ∀ {n} → Expr n → Env n → ℕ
⟦ var x    ⟧ Γ = lookup x Γ
⟦ e₁ ⊕ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ + ⟦ e₂ ⟧ Γ
⟦ suc e    ⟧ Γ = suc (⟦ e ⟧ Γ)
⟦ zero     ⟧ Γ = zero

data Rule (n : ℕ) (lhs rhs : Expr n) : Set where
  rule : (eq : (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
       → Rule n lhs rhs

ruleToProof : {n : ℕ} {lhs rhs : Expr n} → Maybe (Rule n lhs rhs)
            → (Γ : Env n) → Maybe (⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
ruleToProof nothing          Γ = nothing
ruleToProof (just (rule eq)) Γ = just (eq Γ)

plus-Z : Rule 1 (zero ⊕ var zero) (var zero)
plus-Z = rule (λ Γ → refl)

plus-S : Rule 2 (suc (var zero) ⊕ var (suc zero)) (suc (var zero ⊕ var (suc zero)))
plus-S = rule (λ Γ → refl)

rules : List (∃ λ n → ∃₂ (Rule n))
rules = (, , , plus-Z)
      ∷ (, , , plus-S)
      ∷ []

-- Would be nice to get this automatically from rules above (which is the definition of +)
normalize : {n : ℕ} (e : Expr n) → ∃ λ e′ → ∀ Γ → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ
normalize (var x)          = var x , λ _ → refl
normalize (var x ⊕ e₂)     = var x ⊕ (proj₁ (normalize e₂)) , (λ Γ → cong (_+_ (lookup x Γ)) (proj₂ (normalize e₂) Γ))
normalize (suc e₁ ⊕ e₂)    = suc (proj₁ (normalize (e₁ ⊕ e₂))) , (λ Γ → cong suc (proj₂ (normalize (e₁ ⊕ e₂)) Γ))
normalize (zero ⊕ e₂)      = normalize e₂
normalize (suc e)          = (suc (proj₁ (normalize e))) , (λ Γ → cong suc (proj₂ (normalize e) Γ))
normalize zero             = zero , λ _ → refl
normalize ((e₁ ⊕ e₂) ⊕ e₃) with normalize (e₁ ⊕ e₂)
... | e₁' ⊕ e₂' , eq₁₂ = ((e₁' ⊕ e₂') ⊕ proj₁ (normalize e₃)), (λ Γ → cong₂ (_+_) (eq₁₂ Γ) (proj₂ (normalize e₃) Γ))
... | var x      , eq₁₂ = var x ⊕ proj₁ (normalize e₃) , (λ Γ → cong₂ _+_ (eq₁₂ Γ) (proj₂ (normalize e₃) Γ))
... | suc e      , eq₁₂ = suc (e ⊕ proj₁ (normalize e₃)) , (λ Γ → cong₂ _+_ (eq₁₂ Γ) (proj₂ (normalize e₃) Γ))
... | zero       , eq₁₂ = proj₁ (normalize e₃) , (λ Γ → cong₂ _+_ (eq₁₂ Γ) (proj₂ (normalize e₃) Γ))

inst-zero-eval : {n : ℕ} (e : Expr (suc n)) (Γ : Env n)
               → ⟦ inst-zero e ⟧ Γ ≡ ⟦ e ⟧ (0 ∷ Γ)
inst-zero-eval (var zero)    Γ = refl
inst-zero-eval (var (suc i)) Γ = refl
inst-zero-eval (e₁ ⊕ e₂)     Γ = inst-zero-eval e₁ Γ ⟨ cong₂ _+_ ⟩ inst-zero-eval e₂ Γ
inst-zero-eval (suc e)       Γ = cong suc (inst-zero-eval e Γ)
inst-zero-eval zero          Γ = refl

inst-suc-eval : {n : ℕ} (k : ℕ) (e : Expr (suc n)) (Γ : Env n)
               → ⟦ inst-suc e ⟧ (k ∷ Γ) ≡ ⟦ e ⟧ (suc k ∷ Γ)
inst-suc-eval k (var zero)    Γ = refl
inst-suc-eval k (var (suc i)) Γ = refl
inst-suc-eval k (e₁ ⊕ e₂)     Γ = inst-suc-eval k e₁ Γ ⟨ cong₂ _+_ ⟩ inst-suc-eval k e₂ Γ
inst-suc-eval k (suc e)       Γ = cong suc (inst-suc-eval k e Γ)
inst-suc-eval k zero          Γ = refl

induction-inst : {n : ℕ} (lhs rhs : Expr (suc n))
          → (∀ Γ → ⟦ inst-zero lhs ⟧ Γ ≡ ⟦ inst-zero rhs ⟧ Γ)
          → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
                  → ⟦ inst-suc lhs ⟧ Γ ≡ ⟦ inst-suc rhs ⟧ Γ)
           → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
induction-inst lhs rhs p0 ps (zero ∷ Γ) = sym (inst-zero-eval lhs Γ) ⟨ trans ⟩
                                          p0 Γ ⟨ trans ⟩
                                          inst-zero-eval rhs Γ
induction-inst lhs rhs p0 ps (suc k ∷ Γ) = sym (inst-suc-eval k lhs Γ) ⟨ trans ⟩
                                           ps (k ∷ Γ) (induction-inst lhs rhs p0 ps (k ∷ Γ)) ⟨ trans ⟩
                                           inst-suc-eval k rhs Γ

inst-ih : {n : ℕ} (hl hr sl sr : Expr (suc n))
        → Maybe (∀ Γ → ⟦ hl ⟧ Γ ≡ ⟦ hr ⟧ Γ → ⟦ sl ⟧ Γ ≡ ⟦ sr ⟧ Γ)
inst-ih hl hr sl sr with sl ≟-Expr sr | sl ≟-Expr hl | hr ≟-Expr sr
... | yes s-eq | _ | _ = just (λ Γ _ → cong (λ e → ⟦ e ⟧ Γ) s-eq)
... | _ | yes l-eq | yes r-eq = just (λ Γ ih → cong (λ e → ⟦ e ⟧ Γ) l-eq ⟨ trans ⟩ ih ⟨ trans ⟩ cong (λ e → ⟦ e ⟧ Γ) r-eq )
inst-ih hl hr (suc sl)   (suc sr)  | _ | _ | _ with inst-ih hl hr sl sr
... | just p = just (λ Γ ih → cong suc (p Γ ih))
... | nothing = nothing
inst-ih hl hr (l₁ ⊕ l₂) (r₁ ⊕ r₂) | _ | _ | _ with inst-ih hl hr l₁ r₁ | inst-ih hl hr l₂ r₂
... | just p₁ | just p₂ = just (λ Γ ih → cong₂ _+_ (p₁ Γ ih) (p₂ Γ ih))
... | _       | _       = nothing
inst-ih hl hr sl sr | _ | _ | _ = nothing

induction : {n : ℕ} (lhs rhs : Expr (suc n)) → Maybe (Rule (suc n) lhs rhs)
induction lhs rhs with normalize (inst-zero lhs) | normalize (inst-zero rhs)
... | lhs-0 , eq-l-0 | rhs-0 , eq-r-0 with lhs-0 ≟-Expr rhs-0
... | no ¬p = nothing
... | yes p with normalize lhs | normalize rhs | normalize (inst-suc lhs) | normalize (inst-suc rhs)
... | lhs-h , eq-l-h | rhs-h , eq-r-h | lhs-s , eq-l-s | rhs-s , eq-r-s with inst-ih lhs-h rhs-h lhs-s rhs-s
... | just ih-normalized = just (rule (induction-inst lhs rhs
                                           (λ Γ → eq-l-0 Γ ⟨ trans ⟩  cong (λ x → ⟦ x ⟧ Γ) p ⟨ trans ⟩ sym (eq-r-0 Γ))
                                           (λ Γ ih → eq-l-s Γ ⟨ trans ⟩
                                                      ih-normalized Γ (sym (eq-l-h Γ) ⟨ trans ⟩ ih ⟨ trans ⟩ eq-r-h Γ ) ⟨ trans ⟩
                                                      sym (eq-r-s Γ))))
... | nothing = nothing

prove : (n : ℕ) (lhs rhs : Expr n) → Maybe (Rule n lhs rhs)
prove zero    lhs rhs with normalize lhs | normalize rhs
... | lhs′ , eql | rhs′ , eqr with lhs′ ≟-Expr rhs′
... | yes p = just (rule (λ Γ → eql Γ ⟨ trans ⟩ cong (λ e → ⟦ e ⟧ Γ) p ⟨ trans ⟩ sym (eqr Γ)))
... | no ¬p = nothing
prove (suc n) lhs rhs = induction lhs rhs

assoc-plus-vec : (Γ : Env 3) → (lookup (# 0) Γ + (lookup (# 1) Γ + lookup (# 2) Γ)
                             ≡ (lookup (# 0) Γ + lookup (# 1) Γ) + lookup (# 2) Γ)
assoc-plus-vec Γ = from-just (ruleToProof (prove 3 (var zero ⊕ (var (suc zero) ⊕ var (suc (suc zero))))
                                                 ((var zero ⊕ (var (suc zero))) ⊕ var (suc (suc zero)))) Γ)


assoc-plus : ∀ x y z → (x + (y + z) ≡ (x + y) + z)
assoc-plus x y z = assoc-plus-vec (x ∷ y ∷ z ∷ [])

move-suc : ∀ x y → suc x + y ≡ x + suc y
move-suc x y = from-just (ruleToProof (prove 2 (suc (var (# 0)) ⊕ (var (# 1)))
                                               (var (# 0) ⊕ suc (var (# 1))))
                                      (x ∷ y ∷ []))


left-id : ∀ x → x + zero ≡ x
left-id x = from-just (ruleToProof (prove 1 (var (# 0) ⊕ zero) (var (# 0))) (x ∷ []))
