open import Auto.Theory

module Auto.Expr (T : Theory) where

open Theory T

open import Data.Vec hiding ([_])
open import Data.Nat renaming (pred to Nat-pred ; _≟_ to _≟-Nat_)
open import Data.Fin hiding (_+_ ; pred)
open import Data.Fin.Props renaming (_≟_ to _≟-Fin_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary

open import Function

-- Expressions with n variables -----------------------------------------------
data Expr (n : ℕ) : Set where
  zero  : Expr n
  suc   : (e : Expr n)                          → Expr n
  var   : (x : Fin n)                           → Expr n
  _[_]_ : (e₁ : Expr n) (b : Bin) (e₂ : Expr n) → Expr n
  _∙_   : (o : Op) (e : Expr n)                 → Expr n

private
  -- Boring functions to define decidable equality
  unvar : {n : ℕ} {x y : Fin n} → var x ≡ var y → x ≡ y
  unvar refl      = refl

  left : {n : ℕ} → Expr n → Expr n
  left (e₁ [ _ ] _)  = e₁
  left _             = zero

  right : {n : ℕ} → Expr n → Expr n
  right (_ [ _ ] e₂) = e₂
  right (_ ∙ e)      = e
  right _            = zero

  op-bin : {n : ℕ} {e₁ e₂ e₁' e₂' : Expr n} {b b' : Bin}
       → e₁ [ b ] e₂ ≡ e₁' [ b' ] e₂' → b ≡ b'
  op-bin refl = refl

  op-op : {n : ℕ} {e e' : Expr n} {o o' : Op}
       → o ∙ e ≡ o' ∙ e' → o ≡ o'
  op-op refl = refl

  pred : {n : ℕ} → Expr n → Expr n
  pred (suc e)    = e
  pred _          = zero

-- Decidable equality
_≟_ : {n : ℕ} → Decidable {A = Expr n} _≡_
zero          ≟ zero          = yes refl
zero          ≟ suc e         = no λ ()
zero          ≟ var x         = no λ ()
zero          ≟ (e₁ [ b ] e₂) = no λ ()
zero          ≟ (op ∙ e)      = no λ ()
suc e         ≟ zero          = no λ ()
suc e₁        ≟ suc e₂        = map′ (cong suc) (cong pred) (e₁ ≟ e₂)
suc e         ≟ var x         = no λ ()
suc e         ≟ (e₁ [ b ] e₂) = no λ ()
suc e         ≟ (op ∙ e')     = no λ ()
var x         ≟ zero          = no λ ()
var x         ≟ suc e         = no λ ()
var x         ≟ var y         = map′ (cong var) unvar (x ≟-Fin y)
var x         ≟ (e₁ [ b ] e₂) = no λ ()
var x         ≟ (op ∙ e)      = no λ ()
(e₁ [ b ] e₂) ≟ zero          = no λ ()
(e₁ [ b ] e₂) ≟ suc e         = no λ ()
(e₁ [ b ] e₂) ≟ var x         = no λ ()
(e₁ [ b ] e₂) ≟ (e₁' [ b' ] e₂') with e₁ ≟ e₁' | b ≟-Bin b' | e₂ ≟ e₂'
(e₁ [ b ] e₂) ≟ (.e₁ [ .b ] .e₂) | yes refl | yes refl | yes refl = yes refl
...                              | no ¬p    | _        | _        = no (¬p ∘ cong left)
...                              | _        | no ¬p    | _        = no (¬p ∘ op-bin)
...                              | _        | _        | no ¬p    = no (¬p ∘ cong right)
(e₁ [ b ] e₂) ≟ (op ∙ e)       = no λ ()
(op ∙ e)       ≟ zero          = no λ ()
(op ∙ e)       ≟ suc e'        = no λ ()
(op ∙ e)       ≟ var x         = no λ ()
(op ∙ e)       ≟ (e₁ [ b ] e₂) = no λ ()
(op ∙ e)       ≟ (op' ∙ e') with e ≟ e' | op ≟-Op op'
(op ∙ e)       ≟ (.op ∙ .e) | yes refl | yes refl = yes refl
...                         | no ¬p    | _        = no (¬p ∘ cong right)
...                         | _        | no ¬p    = no (¬p ∘ op-op)

-- The environment, a mapping from varibles to natural numbers ----------------
Env : ℕ → Set
Env n = Vec ℕ n

-- Evaluation of an expression for a given environment ------------------------
⟦_⟧ : ∀ {n} → Expr n → Env n → ℕ
⟦ zero        ⟧ Γ = zero
⟦ suc e       ⟧ Γ = suc (⟦ e ⟧ Γ)
⟦ var x       ⟧ Γ = lookup x Γ
⟦ e₁ [ b ] e₂ ⟧ Γ = Bin-eval b (⟦ e₁ ⟧ Γ) (⟦ e₂ ⟧ Γ)
⟦ op ∙ e      ⟧ Γ = Op-eval op (⟦ e ⟧ Γ)
