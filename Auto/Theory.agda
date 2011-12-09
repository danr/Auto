module Auto.Theory where

open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

record Theory : Set₁ where
  field
    U B    : Set
    U-eval : U → ℕ → ℕ
    B-eval : B → ℕ → ℕ → ℕ
    _≟-U_  : Decidable {A = U} _≡_
    _≟-B_  : Decidable {A = B} _≡_
