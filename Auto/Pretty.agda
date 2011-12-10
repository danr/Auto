module Auto.Pretty where

open import Auto.Expr
open import Data.Nat
open import Data.Fin

open import Auto.Theory

data Pretty (U B : Set) (n : ℕ) : Set where
  zero  : Pretty U B n
  suc   : (e : Pretty U B n)                              → Pretty U B n
  var   : (x : Fin n)                                     → Pretty U B n
  _[_]_ : (e₁ : Pretty U B n) (b : B) (e₂ : Pretty U B n) → Pretty U B n
  _∙_   : (u : U) (e : Pretty U B n)                      → Pretty U B n
  x₀ y₁ z₂ : Pretty U B n

pretty : {T : Theory} {n : ℕ}
          → Expr T n → Pretty (Theory.U T) (Theory.B T) n
pretty zero          = zero
pretty (suc e)       = suc (pretty e)
pretty (var zero)                = x₀
pretty (var (suc zero))          = y₁
pretty (var (suc (suc zero)))    = z₂
pretty (var (suc (suc (suc i)))) = var (suc (suc (suc i)))
pretty (e₁ [ b ] e₂) = pretty e₁ [ b ] pretty e₂
pretty (u ∙ e)       = u ∙ pretty e