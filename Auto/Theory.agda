module Auto.Theory where

open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

record Theory : Set₁ where
  field
    Op Bin   : Set
    Op-eval  : Op → ℕ → ℕ
    Bin-eval : Bin → ℕ → ℕ → ℕ
    _≟-Op_   : Decidable {A = Op} _≡_
    _≟-Bin_  : Decidable {A = Bin} _≡_
