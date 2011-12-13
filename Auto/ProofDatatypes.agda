open import Auto.Model

module Auto.ProofDatatypes {T : Theory} (M : Model T) where

open Model M

open import Data.Nat
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Auto.Pretty

-- Equality proof of two expressions under any environment --------------------
Equality : {n : ℕ} (lhs rhs : Expr n) → Set
Equality {n} lhs rhs = (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ

-- Lemmas ---------------------------------------------------------------------
-- Lemma datatype
data Lemma : Set where
  lemma : (n : ℕ) (lhs rhs : Expr n) (eq : Equality lhs rhs) → Lemma

-- Instantiate direction datatype
data LR : Set where
  left right : LR

-- Error messages -------------------------------------------------------------
data Error : Set where
    simplify-failed : {n : ℕ} (lhs rhs : Pretty Op Bin n)     → Error
    step-failed     : {n : ℕ} (hl hr sl sr : Pretty Op Bin n) → Error
    lemma-failed    : {n : ℕ} (e : Pretty Op Bin n)           → Error
    base-failed     : Error                                → Error
    no-lemmas-left  : Error                                → Error

-- Traces ---------------------------------------------------------------------
data Trace : Set where
    _stepPlus_                             : Trace → Trace → Trace
    base⟨_⟩step⟨_⟩                         : Trace → Trace → Trace
    apply                                  : Trace → Trace → Trace
    reshuffle stepSuc                      : Trace → Trace
    refl stepMatchIH stepSideMatch noTrace : Trace
    lemmaStep                              : {n : ℕ} (e : Pretty Op Bin n) → Trace

-- Try (Maybe with traces and error messages) ---------------------------------
data Try {a} (A : Set a) : Set a where
    success : Trace → A → Try A
    fail    : Error → Try A

-- Fmap -----------------------------------------------------------------------

_<$>⟨_⟩_ : {A B : Set} → (A → B) → (Trace → Trace) → Try A → Try B
f <$>⟨ g ⟩ success t a = success (g t) (f a)
f <$>⟨ g ⟩ fail e      = fail e

-- Mplus (so far unused) ------------------------------------------------------

_<+>_ : {A : Set} → Try A → Try A → Try A
success t x <+> _   = success t x
fail _      <+> try = try

-- From just ------------------------------------------------------------------

From-success : (A : Set) → Try A → Set
From-success A (success _ _) = A
From-success A (fail _)      = ⊤

from-success : {A : Set} (x : Try A) → From-success A x
from-success (success _ x) = x
from-success (fail _)      = _
