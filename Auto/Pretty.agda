module Auto.Pretty where

open import Auto.Expr
open import Data.Nat
open import Data.Fin

open import Auto.Theory

data Pretty (Op Bin : Set) (n : ℕ) : Set where
  zero  : Pretty Op Bin n
  suc   : (e : Pretty Op Bin n)                                   → Pretty Op Bin n
  var   : (x : Fin n)                                             → Pretty Op Bin n
  _[_]_ : (e₁ : Pretty Op Bin n) (b : Bin) (e₂ : Pretty Op Bin n) → Pretty Op Bin n
  _∙_   : (u : Op) (e : Pretty Op Bin n)                          → Pretty Op Bin n
  x₀ y₁ z₂ : Pretty Op Bin n

pretty : {T : Theory} {n : ℕ}
          → Expr T n → Pretty (Theory.Op T) (Theory.Bin T) n
pretty zero          = zero
pretty (suc e)       = suc (pretty e)
pretty (var zero)                = x₀
pretty (var (suc zero))          = y₁
pretty (var (suc (suc zero)))    = z₂
pretty (var (suc (suc (suc i)))) = var (suc (suc (suc i)))
pretty (e₁ [ b ] e₂) = pretty e₁ [ b ] pretty e₂
pretty (op ∙ e)      = op ∙ pretty e