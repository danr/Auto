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

data Op : Set where
  Double : Op

_≟-Op_ : Decidable {A = Op} _≡_
Double ≟-Op Double    = yes refl

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
example-theory = record { Op = Op
                        ; Bin = Bin
                        ; Op-eval = λ { Double → double }
                        ; Bin-eval = λ { ⊕ → _+_ ; ⊛ → _*_ }
                        ; _≟-Op_ = _≟-Op_
                        ; _≟-Bin_ = _≟-Bin_
                        }

example-model : Model example-theory
example-model = record { bin-normalize         = λ { ⊕ → _⨁_ ; ⊛ → _⨂_ }
                       ; bin-normalize-correct = λ { ⊕ → ⨁-correct ; ⊛ → ⨂-correct }
                       ; op-normalize          = λ { Double → dbl         }
                       ; op-normalize-correct  = λ { Double → dbl-correct }
                       }
  where
    import Auto.Expr as E
    open E example-theory
    open Theory example-theory

    dbl : {n : ℕ} → Expr n → Expr n
    dbl zero       = zero
    dbl (suc e)    = suc (suc (dbl e))
    dbl e          = Double ∙ e

    dbl-correct : {n : ℕ} (e : Expr n) (Γ : Env n)
                → ⟦ Double ∙ e ⟧ Γ ≡ ⟦ dbl e ⟧ Γ
    dbl-correct zero          Γ = refl
    dbl-correct (suc e)       Γ = cong (suc ∘′ suc) (dbl-correct e Γ)
    dbl-correct (var x)       Γ = refl
    dbl-correct (e₁ [ b ] e₂) Γ = refl
    dbl-correct (u ∙ e)       Γ = refl

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
