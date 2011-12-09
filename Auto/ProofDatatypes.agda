module Auto.ProofDatatypes where

open import Data.Nat
open import Data.Unit
open import Auto.Expr
open import Relation.Binary.PropositionalEquality

-- Equality proof of two expressions under any environment --------------------
Equality : {n : ℕ} (lhs rhs : Expr n) → Set
Equality {n} lhs rhs = (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ

data Error : Set where
    simp-failed    : {n : ℕ} (lhs rhs : Expr n)     → Error
    step-failed    : {n : ℕ} (hl hr sl sr : Expr n) → Error
    lemma-failed   : {n : ℕ} (e : Expr n)           → Error
    base-failed    : Error                          → Error
    no-lemmas-left : Error                          → Error

data Try (A : Set) : Set where
    success : A → Try A
    fail    : Error → Try A

_<$>_ : {A B : Set} → (A → B) → Try A → Try B
f <$> success a = success (f a)
f <$> fail e    = fail e

_<+>_ : {A : Set} → Try A → Try A → Try A
success x <+> _   = success x
fail _    <+> try = try

From-success : (A : Set) → Try A → Set
From-success A (success _) = A
From-success A (fail _)    = ⊤

from-success : {A : Set} (x : Try A) → From-success A x
from-success (success x) = x
from-success (fail _)    = _
