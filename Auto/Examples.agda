module Auto.Examples where

open import Auto.Model
open import Auto.ExampleModel

open import Data.Vec hiding ([_])
open import Data.List hiding ([_])
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality

open Model example-model

import Auto.Induction      as I ; open I example-model
import Auto.ProofDatatypes as ‵ ; open ‵ example-model

open import Auto.Pretty

-- Some examples --------------------------------------------------------------

_+′_ : ∀ {n} → Expr n → Expr n → Expr n
e₁ +′ e₂ = e₁ [ ⊕ ] e₂

_*′_ : ∀ {n} → Expr n → Expr n → Expr n
e₁ *′ e₂ = e₁ [ ⊛ ] e₂

-- Associativity of plus ------------------------------------------------------

assoc-plus-proof = prove′ 3 (λ x y z → x +′ (y +′ z) == (x +′ y) +′ z)

assoc-plus : ∀ x y z → x + (y + z) ≡ (x + y) + z
assoc-plus = from-success assoc-plus-proof

-- Left identity for plus -----------------------------------------------------
left-id : ∀ x → x ≡ x + zero
left-id = from-success (prove′ 1 (λ x → x == x +′ zero))

*-left-id-proof = prove′ 1 (λ x → x == x *′ suc zero)

*-left-id : ∀ x → x ≡ x * suc zero
*-left-id = from-success *-left-id-proof

*-right-id : ∀ x → x ≡ suc zero * x
*-right-id = from-success (prove′ 1 (λ x → x == suc zero *′ x))

-- Grand finale: commutativity of plus ----------------------------------------

-- Some lemmas:  move-suc
move-suc-lhs : Expr 2
move-suc-lhs = suc (var (# 1) [ ⊕ ] (var (# 0)))

move-suc-rhs : Expr 2
move-suc-rhs = var (# 1) [ ⊕ ] suc (var (# 0))

-- Need induction on y to prove this
move-suc = prove-with-induction-on 2 (# 1) move-suc-lhs move-suc-rhs

move-suc-lemma : Lemma
move-suc-lemma = lemma 2 move-suc-lhs move-suc-rhs (from-success move-suc)

-- Left idenity lemma
left-id-lemma : Lemma
left-id-lemma = from-success (lemma′ 1 (λ x → x == x +′ zero))

-- Commutativity of plus.
comm-plus : ∀ x y → x + y ≡ y + x
comm-plus x y = from-success (prove-with-lemmas
                                 2
                                 -- ^ two variables
                                 (var (# 0) [ ⊕ ] var (# 1))
                                 -- ^ lhs
                                 (var (# 1) [ ⊕ ] var (# 0))
                                 -- ^ rhs
                                 1
                                 -- ^ we only need to instantate lemmas once
                                 (move-suc-lemma ∷ left-id-lemma ∷ []))
                                 -- ^ lemmas to use
                          (x ∷ y ∷ [])

comm-plus′ = prove-with-lemmas 2
                               -- ^ two variables
                               (var (# 0) [ ⊕ ] var (# 1))
                               -- ^ lhs
                               (var (# 1) [ ⊕ ] var (# 0))
                               -- ^ rhs
                               1
                               -- ^ we only need to instantate lemmas once
                               (move-suc-lemma ∷ left-id-lemma ∷ [])
                               -- ^ lemmas to use

comm-plus-lemma = lemma 2 (var (# 0) [ ⊕ ] var (# 1)) (var (# 1) [ ⊕ ] var (# 0)) (from-success comm-plus′)

mul-0-lemma = from-success (lemma′ 1 (λ x → zero == x *′ zero))

*-comm-proof = prove-with-lemmas 2 (var (# 0) [ ⊛ ] var (# 1))
                                   (var (# 1) [ ⊛ ] var (# 0))
                                 2 (mul-0-lemma ∷ [])
-- ^ stuck at y + (x * y) ≡ y * suc x
--                ^ instantiate IH here!
