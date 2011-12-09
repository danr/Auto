-- Automatic induction for a simple language with +, suc, zero and variables --
module Auto.Expr where

open import Data.Vec
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
  var  : (x : Fin n)      → Expr n
  _⊕_  : (e₁ e₂ : Expr n) → Expr n
  suc  : (e : Expr n)     → Expr n
  zero : Expr n

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

-- The environment, a mapping from varibles to natural numbers ----------------
Env : ℕ → Set
Env n = Vec ℕ n

-- Evaluation of an expression for a given environment ------------------------
⟦_⟧ : ∀ {n} → Expr n → Env n → ℕ
⟦ var x   ⟧ Γ = lookup x Γ
⟦ e₁ ⊕ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ + ⟦ e₂ ⟧ Γ
⟦ suc e   ⟧ Γ = suc (⟦ e ⟧ Γ)
⟦ zero    ⟧ Γ = zero

