module Auto.Demo where

open import Auto.Model
open import Auto.Pretty
open import Auto.ExampleModel

import Auto.Expr           as E; open E example-theory
import Auto.ProofDatatypes as `; open ` example-model
import Auto.Induction      as I; open I example-model

open import Data.Nat
open import Data.Fin hiding (_+_)

open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding ([_])
open import Data.List hiding ([_])

_+′_ : {n : ℕ} → Expr n → Expr n → Expr n
e₁ +′ e₂ = e₁ [ ⊕ ] e₂

_*′_ : {n : ℕ} → Expr n → Expr n → Expr n
e₁ *′ e₂ = e₁ [ ⊛ ] e₂

------------------------------------------------------------------------------

plus-assoc-proof = prove 3 (λ x y z → x +′ (y +′ z) == (x +′ y) +′ z)

plus-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
plus-assoc = from-success plus-assoc-proof

mul-identity-proof = prove 1 (λ x → x == x *′ suc zero)

mul-identity : ∀ x → x ≡ x * 1
mul-identity = from-success mul-identity-proof

------------------------------------------------------------------------------

plus-identity-lemma = lemma 1 (λ x → x == x +′ zero)

move-suc-lemma = lemma-with-induction-on 2 (# 1) (λ x y → suc (y +′ x) == y +′ suc x)

plus-comm-proof = prove-with-lemmas 2 (λ x y → x +′ y == y +′ x)
                   1 ( from-success plus-identity-lemma
                      ∷ from-success move-suc-lemma
                      ∷ [])

plus-comm : ∀ x y → x + y ≡ y + x
plus-comm = from-success plus-comm-proof

------------------------------------------------------------------------------

open import Data.Unit

unit : ⊤
unit = from-success (prove 1 (λ x → x +′ x == x))

------------------------------------------------------------------------------

mul-comm-proof = prove-with-lemmas 2 (λ x y → x *′ y == y *′ x)
                   1 ( from-success (lemma 1 (λ x → zero == x *′ zero))
                     ∷ [])