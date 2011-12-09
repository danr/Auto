module Auto.Examples where

open import Auto.Model
open import Auto.ExampleModel

open import Data.Vec hiding ([_])
open import Data.List hiding ([_])
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat

open import Relation.Binary.PropositionalEquality

-- open Model example-model

import Auto.Induction      as I  ; open I  example-model
import Auto.ProofDatatypes as PD ; open PD example-model
import Auto.Expr           as E  ; open E  example-theory

-- Some examples --------------------------------------------------------------

-- Associativity of plus ------------------------------------------------------
-- This is how it looks if you use the vector
assoc-plus-vec : (Γ : Env 3) → lookup (# 0) Γ + (lookup (# 1) Γ + lookup (# 2) Γ)
                             ≡ (lookup (# 0) Γ + lookup (# 1) Γ) + lookup (# 2) Γ
assoc-plus-vec Γ = from-success (prove 3 (var (# 0) [ ⊕ ] (var (# 1) [ ⊕ ] var (# 2)))
                                         ((var (# 0) [ ⊕ ] (var (# 1))) [ ⊕ ] var (# 2))
                                         ) Γ

-- But you can also specify the vector like this
assoc-plus : ∀ x y z → x + (y + z) ≡ (x + y) + z
assoc-plus x y z = assoc-plus-vec (x ∷ y ∷ z ∷ [])

-- Left identity for plus -----------------------------------------------------
left-id : ∀ x → x ≡ x + zero
left-id x = from-success (prove 1 (var (# 0)) (var (# 0) [ ⊕ ] zero)) (x ∷ [])



*-left-id-proof = prove 1 (var (# 0)) (var (# 0) [ ⊛ ] suc zero)

*-left-id : ∀ x → x ≡ x * suc zero
*-left-id x = from-success *-left-id-proof (x ∷ [])

*-right-id : ∀ x → x ≡ suc zero * x
*-right-id x = from-success (prove 1 (var (# 0)) (suc zero [ ⊛ ] var (# 0))) (x ∷ [])

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
left-id-lhs : Expr 1
left-id-lhs = var (# 0)

left-id-rhs : Expr 1
left-id-rhs = var (# 0) [ ⊕ ] zero

left-id-lemma : Lemma
left-id-lemma = lemma 1 left-id-lhs left-id-rhs
                        (from-success (prove 1 left-id-lhs left-id-rhs))

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

mul-0-proof = prove 1 zero (var (# 0) [ ⊛ ] zero)

*-comm-proof = prove-with-lemmas 2 (var (# 0) [ ⊛ ] var (# 1))
                                   (var (# 1) [ ⊛ ] var (# 0))
                                 1 (lemma 1 zero (var (# 0) [ ⊛ ] zero) (from-success mul-0-proof) ∷ [])
-- ^ stuck at y + (x * y) ≡ y * suc x (must have used the induction hypothesis once)
