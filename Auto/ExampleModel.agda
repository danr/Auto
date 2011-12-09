module Auto.ExampleModel where

open import Data.Vec hiding ([_])
open import Data.List hiding ([_])
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Function

open import Auto.Model

data Un : Set where
--  Double Factorial : Un

_≟-Un_ : Decidable {A = Un} _≡_
() ≟-Un ()
{-
Double    ≟-Un Double    = yes refl
Double    ≟-Un Factorial = no λ ()
Factorial ≟-Un Double    = no λ ()
Factorial ≟-Un Factorial = yes refl
-}

data Bin : Set where
  ⊕ ⊛ : Bin

_≟-Bin_ : Decidable {A = Bin} _≡_
⊕ ≟-Bin ⊕ = yes refl
⊕ ≟-Bin ⊛ = no λ ()
⊛ ≟-Bin ⊕ = no λ ()
⊛ ≟-Bin ⊛ = yes refl

double : ℕ → ℕ
double zero    = zero
double (suc x) = suc (suc (double x))

factorial : ℕ → ℕ
factorial zero = suc zero
factorial (suc x) = suc x * factorial x

example-theory : Theory
example-theory = record { U = Un
                        ; B = Bin
                        ; U-eval = λ ()
                        ; B-eval = λ { ⊕ → _+_ ; ⊛ → _*_ }
                        ; _≟-U_ = _≟-Un_
                        ; _≟-B_ = _≟-Bin_
                        }

example-model : Model example-theory
example-model = record {
                  bin-normalize         = λ { ⊕ → _⨁_ ; ⊛ → _⨂_ };
                  bin-normalize-correct = λ { ⊕ → ⨁-correct ; ⊛ → ⨂-correct };
                  un-normalize          = λ ();
                  un-normalize-correct  = λ () }
  where
    import Auto.Expr as E
    open E example-theory
    open Theory example-theory

    _⨁_ : {n : ℕ} → Expr n → Expr n → Expr n
    -- Definition of plus
    zero      ⨁ e₂ = e₂
    suc e₁    ⨁ e₂ = suc (e₁ ⨁ e₂)
    -- Nothing special here
    e₁        ⨁ e₂ = e₁ [ ⊕ ] e₂

    ⨁-correct : {n : ℕ} (e₁ e₂ : Expr n) (Γ : Env n)
               → ⟦ e₁ [ ⊕ ] e₂ ⟧ Γ ≡ ⟦ e₁ ⨁ e₂ ⟧ Γ
    ⨁-correct (suc e)       e₂ Γ = cong suc (⨁-correct e e₂ Γ)
    ⨁-correct zero          e₂ Γ = refl
    ⨁-correct (var x)       e₂ Γ = refl
    ⨁-correct (u ∙ e₁)      e₂ Γ = refl
    ⨁-correct (e₁ [ b ] e₂) e₃ Γ = refl

    _⨂_ : {n : ℕ} → Expr n → Expr n → Expr n
    -- Definition of multiplication
    zero      ⨂ e₂ = zero
    suc e₁    ⨂ e₂ = e₂ ⨁ (e₁ ⨂ e₂)
    -- Nothing special here
    e₁        ⨂ e₂ = e₁ [ ⊛ ] e₂

    ⨂-correct : {n : ℕ} (e₁ e₂ : Expr n) (Γ : Env n)
               → ⟦ e₁ [ ⊛ ] e₂ ⟧ Γ ≡ ⟦ e₁ ⨂ e₂ ⟧ Γ
    ⨂-correct (suc e₁)      e₂ Γ = cong (_+_ (⟦ e₂ ⟧ Γ)) (⨂-correct e₁ e₂ Γ) ⟨ trans ⟩ ⨁-correct e₂ (e₁ ⨂ e₂) Γ
    ⨂-correct zero          e₂ Γ = refl
    ⨂-correct (var x)       e₂ Γ = refl
    ⨂-correct (u ∙ e₁)      e₂ Γ = refl
    ⨂-correct (e₁ [ b ] e₂) e₃ Γ = refl

