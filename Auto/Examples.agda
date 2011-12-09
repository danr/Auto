module Auto.Examples where

open import Data.Vec
open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Auto.Expr
open import Auto.Induction

-- Some examples --------------------------------------------------------------

-- Associativity of plus ------------------------------------------------------
-- This is how it looks if you use the vector
assoc-plus-vec : (Γ : Env 3) → lookup (# 0) Γ + (lookup (# 1) Γ + lookup (# 2) Γ)
                             ≡ (lookup (# 0) Γ + lookup (# 1) Γ) + lookup (# 2) Γ
assoc-plus-vec Γ = from-just (prove 3 (var (# 0) ⊕ (var (# 1) ⊕ var (# 2)))
                                      ((var (# 0) ⊕ (var (# 1))) ⊕ var (# 2))
                                      ) Γ
n
-- But you can also specify the vector like this
assoc-plus : ∀ x y z → x + (y + z) ≡ (x + y) + z
assoc-plus x y z = assoc-plus-vec (x ∷ y ∷ z ∷ [])

-- Infamous move-suc lemma ----------------------------------------------------
move-suc : ∀ x y → suc (x + y) ≡ x + suc y
move-suc x y = from-just (prove 2 (suc (var (# 0) ⊕ (var (# 1))))
                                  (var (# 0) ⊕ suc (var (# 1))))
                                  (x ∷ y ∷ [])

-- Left identity for plus -----------------------------------------------------
left-id : ∀ x → x ≡ x + zero
left-id x = from-just (prove 1 (var (# 0)) (var (# 0) ⊕ zero)) (x ∷ [])

-- Grand finale: commutativity of plus ----------------------------------------

-- Some lemmas:  move-suc
move-suc-lhs : Expr 2
move-suc-lhs = suc (var (# 1) ⊕ (var (# 0)))

move-suc-rhs : Expr 2
move-suc-rhs = var (# 1) ⊕ suc (var (# 0))

-- This is a bit cheating, we actually need to instantiate them with
-- the arguments flipped. Real solution: use unification.
move-suc-lemma : Lemma
move-suc-lemma = lemma 2 move-suc-lhs move-suc-rhs
                         (λ Γ → move-suc (lookup (suc zero) Γ) (lookup zero Γ))

-- Left idenity lemma
left-id-lhs : Expr 1
left-id-lhs = var (# 0)

left-id-rhs : Expr 1
left-id-rhs = var (# 0) ⊕ zero

left-id-lemma : Lemma
left-id-lemma = lemma 1 left-id-lhs left-id-rhs
                        (from-just (prove 1 left-id-lhs left-id-rhs))

-- Commutativity of plus.
comm-plus : ∀ x y → x + y ≡ y + x
comm-plus x y = from-just (prove-with-lemmas 1
                             -- ^ we only need to instantate lemmas once -}
                             (move-suc-lemma ∷ left-id-lemma ∷ [])
                             -- ^ lemmas to use
                             2
                             -- ^ two variables
                             (var (# 0) ⊕ var (# 1))
                             -- ^ lhs
                             (var (# 1) ⊕ var (# 0)))
                             -- ^ rhs
                          (x ∷ y ∷ [])

