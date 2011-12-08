-- Automatic induction for a simple language with +, suc, zero and variables --
module Auto where

open import Data.Vec
open import Data.Nat renaming (pred to Nat-pred ; _≟_ to _≟-Nat_)
open import Data.Fin hiding (_+_ ; pred)
open import Data.Fin.Props renaming (_≟_ to _≟-Fin_)
open import Data.List hiding (replicate)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Vec.N-ary
open import Data.Maybe renaming (functor to maybe-functor)
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Function

open import Category.Functor
import Level

open RawFunctor (maybe-functor {Level.zero})

-- Expressions with n variables -----------------------------------------------
data Expr (n : ℕ) : Set where
  var  : (x : Fin n)      → Expr n
  _⊕_  : (e₁ e₂ : Expr n) → Expr n
  suc  : (e : Expr n)     → Expr n
  zero : Expr n

-- Decidable Equality (in a module to hide some boring functions) -------------
module DecidableEquality where
  private
    -- Boring functions to define decidable equality
    unvar : {n : ℕ} {x y : Fin n} → var x ≡ var y → x ≡ y
    unvar refl      = refl

    left : {n : ℕ} → Expr n → Expr n
    left (e₁ ⊕ e₂)  = e₁
    left _          = zero

    right : {n : ℕ} → Expr n → Expr n
    right (e₁ ⊕ e₂) = e₂
    right _         = zero

    pred : {n : ℕ} → Expr n → Expr n
    pred (suc e)    = e
    pred _          = zero

  -- Decidable equality
  _≟_ : {n : ℕ} → Decidable {A = Expr n} _≡_
  var x     ≟ var y     = map′ (cong var) unvar (x ≟-Fin y)
  var x     ≟ (e₁ ⊕ e₂) = no λ ()
  var x     ≟ suc e     = no λ ()
  var x     ≟ zero      = no λ ()
  (e₁ ⊕ e₂) ≟ var x     = no λ ()
  (e₁ ⊕ e₂) ≟ (e₁′ ⊕ e₂′) with e₁ ≟ e₁′ | e₂ ≟ e₂′
  (e₁ ⊕ e₂) ≟ (.e₁ ⊕ .e₂) | yes refl | yes refl = yes refl
  ...                     | no ¬p    | _        = no (¬p ∘ cong left)
  ...                     | _        | no ¬p    = no (¬p ∘ cong right)
  (e₁ ⊕ e₂) ≟ suc e     = no λ ()
  (e₁ ⊕ e₂) ≟ zero      = no λ ()
  suc e     ≟ var x     = no λ ()
  suc e     ≟ (e₁ ⊕ e₂) = no λ ()
  suc e     ≟ suc e'    = map′ (cong suc) (cong pred) (e ≟ e')
  suc e     ≟ zero      = no λ ()
  zero      ≟ var x     = no λ ()
  zero      ≟ (e₁ ⊕ e₂) = no λ ()
  zero      ≟ suc e     = no λ ()
  zero      ≟ zero      = yes refl

open DecidableEquality

-- The environment, a mapping from varibles to natural numbers ----------------
Env : ℕ → Set
Env n = Vec ℕ n

-- Evaluation of an expression for a given environment ------------------------
⟦_⟧ : ∀ {n} → Expr n → Env n → ℕ
⟦ var x   ⟧ Γ = lookup x Γ
⟦ e₁ ⊕ e₂ ⟧ Γ = ⟦ e₁ ⟧ Γ + ⟦ e₂ ⟧ Γ
⟦ suc e   ⟧ Γ = suc (⟦ e ⟧ Γ)
⟦ zero    ⟧ Γ = zero

-- Normalization of plus ------------------------------------------------------
_⨁_ : {n : ℕ} → Expr n → Expr n → Expr n
-- Definition of plus
suc e     ⨁ e₂ = suc (e ⨁ e₂)
zero      ⨁ e₂ = e₂
-- Nothing special here
var x     ⨁ e₂ = var x ⊕ e₂
(e₁ ⊕ e₂) ⨁ e₃ = (e₁ ⊕ e₂) ⊕ e₃

⨁-correct : {n : ℕ} (e₁ e₂ : Expr n) (Γ : Env n)
           → ⟦ e₁ ⊕ e₂ ⟧ Γ ≡ ⟦ e₁ ⨁ e₂ ⟧ Γ
⨁-correct (suc e)   e₂ Γ = cong suc (⨁-correct e e₂ Γ)
⨁-correct zero      e₂ Γ = refl
⨁-correct (var x)   e₂ Γ = refl
⨁-correct (e₁ ⊕ e₂) e₃ Γ = refl

-- Normalization of an expression ---------------------------------------------
-- How would one prove completeness?
normalize : {n : ℕ} (e : Expr n) → Expr n
normalize (var x)   = var x
normalize (e₁ ⊕ e₂) = normalize e₁ ⨁ normalize e₂
normalize (suc e)   = suc (normalize e)
normalize zero      = zero

normalize-correct : {n : ℕ} (e : Expr n) (Γ : Env n)
                  → ⟦ e ⟧ Γ ≡ ⟦ normalize e ⟧ Γ
normalize-correct (var x)   Γ = refl
normalize-correct (e₁ ⊕ e₂) Γ = normalize-correct e₁ Γ ⟨ cong₂ _+_ ⟩ normalize-correct e₂ Γ ⟨ trans ⟩
                                ⨁-correct (normalize e₁) (normalize e₂) Γ
normalize-correct (suc e)   Γ = cong suc (normalize-correct e Γ)
normalize-correct zero      Γ = refl

normalize-with-correct : {n : ℕ} (e : Expr n) → ∃ λ e′ → ∀ Γ → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ
normalize-with-correct e = normalize e , normalize-correct e

{-
-- A little failed attempt to show completeness.
-- It should be complete wrt Agda's normalization, but I am not sure
-- how to capture this in a type.

lookup-replicate : {n : ℕ} (x : Fin n) (v : ℕ)
                 → v ≡ lookup x (replicate v)
lookup-replicate zero    v = refl
lookup-replicate (suc i) v = lookup-replicate i v

normalize-complete : {n : ℕ} (e : Expr n) (e′ : Expr n)
                   → ((Γ : Env n) → ⟦ e ⟧ Γ ≡ ⟦ e′ ⟧ Γ)
                   → normalize e ≡ normalize e′
normalize-complete (var x) (var y  ⊕ zero) eq with x ≟-Fin y
normalize-complete (var x) (var .x ⊕ zero) eq | yes refl = {!!}
-- ^ this is why it is not complete in this sense
--   Goal: var x ≡ var x ⊕ zero
normalize-complete (var x) (var y  ⊕ zero) eq | no ¬p = {!!}
normalize-complete e e′ eq = {!!}
-}

-- Induction instantiation ----------------------------------------------------

-- Replace variable 0 with constant zero
inst-zero : {n : ℕ} → Expr (suc n) → Expr n
inst-zero (var zero)    = zero
inst-zero (var (suc i)) = var i
inst-zero (e₁ ⊕ e₂)     = inst-zero e₁ ⊕ inst-zero e₂
inst-zero (suc e)       = suc (inst-zero e)
inst-zero zero          = zero

-- This operation preserves equality under evaluation
inst-zero-correct : {n : ℕ} (e : Expr (suc n)) (Γ : Env n)
               → ⟦ inst-zero e ⟧ Γ ≡ ⟦ e ⟧ (0 ∷ Γ)
inst-zero-correct (var zero)    Γ = refl
inst-zero-correct (var (suc i)) Γ = refl
inst-zero-correct (e₁ ⊕ e₂)     Γ = inst-zero-correct e₁ Γ ⟨ cong₂ _+_ ⟩ inst-zero-correct e₂ Γ
inst-zero-correct (suc e)       Γ = cong suc (inst-zero-correct e Γ)
inst-zero-correct zero          Γ = refl

-- Replace variable 0 with suc of the variable
inst-suc : {n : ℕ} → Expr (suc n) → Expr (suc n)
inst-suc (var zero)    = suc (var zero)
inst-suc (var (suc i)) = var (suc i)
inst-suc (e₁ ⊕ e₂)     = inst-suc e₁ ⊕ inst-suc e₂
inst-suc (suc e)       = suc (inst-suc e)
inst-suc zero          = zero

-- This operation preserves equality under evaluation
inst-suc-correct : {n : ℕ} (k : ℕ) (e : Expr (suc n)) (Γ : Env n)
              → ⟦ inst-suc e ⟧ (k ∷ Γ) ≡ ⟦ e ⟧ (suc k ∷ Γ)
inst-suc-correct k (var zero)    Γ = refl
inst-suc-correct k (var (suc i)) Γ = refl
inst-suc-correct k (e₁ ⊕ e₂)     Γ = inst-suc-correct k e₁ Γ ⟨ cong₂ _+_ ⟩ inst-suc-correct k e₂ Γ
inst-suc-correct k (suc e)       Γ = cong suc (inst-suc-correct k e Γ)
inst-suc-correct k zero          Γ = refl

-- Equality proof of two expressions under any environment --------------------
Equality : {n : ℕ} (lhs rhs : Expr n) → Set
Equality {n} lhs rhs = (Γ : Env n) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ

-- Induction ------------------------------------------------------------------
induction-inst : {n : ℕ} (lhs rhs : Expr (suc n))
               → (∀ Γ → ⟦ inst-zero lhs ⟧ Γ ≡ ⟦ inst-zero rhs ⟧ Γ)
               → (∀ Γ → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ
                      → ⟦ inst-suc lhs ⟧ Γ ≡ ⟦ inst-suc rhs ⟧ Γ)
               → Equality lhs rhs
induction-inst lhs rhs p0 ps (zero ∷ Γ)  = sym (inst-zero-correct lhs Γ) ⟨ trans ⟩
                                           p0 Γ                       ⟨ trans ⟩
                                           inst-zero-correct rhs Γ
induction-inst lhs rhs p0 ps (suc k ∷ Γ) = sym (inst-suc-correct k lhs Γ)                       ⟨ trans ⟩
                                           ps (k ∷ Γ) (induction-inst lhs rhs p0 ps (k ∷ Γ)) ⟨ trans ⟩
                                           inst-suc-correct k rhs Γ

-- If the expressions are equal, then so is evaluating them under the same environment
cong-⟦─⟧ : {n : ℕ} {e₁ e₂ : Expr n} (Γ : Env n) → e₁ ≡ e₂ → ⟦ e₁ ⟧ Γ ≡ ⟦ e₂ ⟧ Γ
cong-⟦─⟧ Γ = cong (λ e → ⟦ e ⟧ Γ)

-- Lemmas ---------------------------------------------------------------------
-- Lemma datatype
data Lemma : Set where
  lemma : (n : ℕ) (lhs rhs : Expr n) (eq : Equality lhs rhs) → Lemma

-- Instantiate direction datatype
data LR : Set where
  left right : LR

-- Instantiates the first lemma that matches in the given direction
inst-lemma : {n : ℕ} → LR → List Lemma → (e : Expr n) → Maybe (∃ (Equality e))
inst-lemma     lr []                       e = nothing
inst-lemma {n} lr (lemma m lhs rhs eq ∷ ls) e with n ≟-Nat m
... | no ¬p = inst-lemma lr ls e
inst-lemma lr    (lemma m lhs rhs eq ∷ ls) e | yes refl with e ≟ lhs | e ≟ rhs
inst-lemma left  (lemma m lhs rhs eq ∷ ls) e | yes refl | yes p | _ = just (rhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ eq Γ)
inst-lemma right (lemma m lhs rhs eq ∷ ls) e | yes refl | _ | yes p = just (lhs , λ Γ → cong-⟦─⟧ Γ p ⟨ trans ⟩ sym (eq Γ))
... | _ | _ = inst-lemma lr ls e

-- Instantiate the induction hypothesis. Match the goal with the given. -------
inst-ih : {n : ℕ}
        → ℕ → List Lemma
        → (hl hr sl sr : Expr (suc n))
        → Maybe (∀ Γ → ⟦ hl ⟧ Γ ≡ ⟦ hr ⟧ Γ → ⟦ sl ⟧ Γ ≡ ⟦ sr ⟧ Γ)
inst-ih uses lemmas hl hr sl sr with sl ≟ sr | sl ≟ hl | hr ≟ sr
-- The step sides match
... | yes s-eq | _        | _        = just λ Γ _  → cong-⟦─⟧ Γ s-eq
-- The step sides match the induction hypothesis
... | _        | yes l-eq | yes r-eq = just λ Γ ih → cong-⟦─⟧ Γ l-eq ⟨ trans ⟩ ih ⟨ trans ⟩ cong-⟦─⟧ Γ r-eq
{-
-- The left step side match the induction hypothesis  (this could be nice to use)
... | _        | yes l-eq | no ¬p    = ...
-- The right step side match the induction hypothesis (this could be nice to use)
... | _        | no ¬p    | yes r-eq = ...
-}
-- The step sides both start with suc
inst-ih uses lemmas hl hr (suc sl)  (suc sr)  | _ | _ | _ with inst-ih uses lemmas hl hr sl sr
... | just p  = just λ Γ ih → cong suc (p Γ ih)
... | nothing = nothing
-- The step sides both start with ⊕
inst-ih uses lemmas hl hr (l₁ ⊕ l₂) (r₁ ⊕ r₂) | _ | _ | _ with inst-ih uses lemmas hl hr l₁ r₁ | inst-ih uses lemmas hl hr l₂ r₂
... | just p₁ | just p₂ = just λ Γ ih → p₁ Γ ih ⟨ cong₂ _+_ ⟩ p₂ Γ ih
... | _       | _       = nothing
-- No lemmas uses left
inst-ih zero         lemmas hl hr sl sr | _ | _ | _ = nothing
-- Instantiate a lemma
inst-ih (suc uses-1) lemmas hl hr sl sr | _ | _ | _ with inst-lemma left lemmas sl | inst-lemma right lemmas sr
... | just (sl′ , sl≡sl′) | _ = (λ ih' Γ ih → sl≡sl′ Γ ⟨ trans ⟩ ih' Γ ih)
                                <$> inst-ih uses-1 lemmas hl hr sl′ sr
... | _ | just (sr′ , sr≡sr′) = (λ ih' Γ ih → ih' Γ ih ⟨ trans ⟩ sym (sr≡sr′ Γ))
                                <$> inst-ih uses-1 lemmas hl hr sl sr′
... | _ | _ = nothing

-- Simplification. ------------------------------------------------------------
-- Used for the base case and for proving equality with no variables
simp : {n : ℕ}
     → ℕ → List Lemma
     → (lhs rhs : Expr n)
     -- ^ normalized lhs and rhs
     → Maybe (Equality lhs rhs)
simp uses lemmas lhs rhs with lhs ≟ rhs
-- lhs ≡ rhs by reflexivity
... | yes p = just (λ Γ → cong-⟦─⟧ Γ p)
-- No lemma uses left
simp zero         lemmas lhs rhs | no ¬p = nothing
-- Try to use a lemma
simp (suc uses-1) lemmas lhs rhs | no ¬p with inst-lemma left lemmas lhs | inst-lemma right lemmas rhs
... | just (lhs′ , lhs≡lhs′) | _ = (λ x Γ → lhs≡lhs′ Γ ⟨ trans ⟩ x Γ) <$> simp uses-1 lemmas lhs′ rhs
... | _ | just (rhs′ , rhs≡rhs′) = (λ x Γ → x Γ ⟨ trans ⟩ sym (rhs≡rhs′ Γ)) <$> simp uses-1 lemmas lhs rhs′
... | _ | _ = nothing

-- Induction on the first variable --------------------------------------------
induction : {n : ℕ}
          → ℕ → List Lemma
          → (lhs rhs : Expr (suc n)) → Maybe (Equality lhs rhs)
induction uses lemmas lhs rhs with normalize-with-correct (inst-zero lhs) | normalize-with-correct (inst-zero rhs)
... | lhs-0 , eq-l-0 | rhs-0 , eq-r-0 with simp uses lemmas lhs-0 rhs-0
-- Base case failed
... | nothing = nothing
-- Base case suceeded
... | just base with normalize-with-correct lhs | normalize-with-correct rhs | normalize-with-correct (inst-suc lhs) | normalize-with-correct (inst-suc rhs)
... | lhs-h , eq-l-h | rhs-h , eq-r-h | lhs-s , eq-l-s | rhs-s , eq-r-s with inst-ih uses lemmas lhs-h rhs-h lhs-s rhs-s
-- Induction step suceeded
... | just ih-normalized = just (induction-inst lhs rhs
                                    (λ Γ → eq-l-0 Γ ⟨ trans ⟩ base Γ ⟨ trans ⟩ sym (eq-r-0 Γ))
                                    (λ Γ ih → eq-l-s Γ                        ⟨ trans ⟩
                                              ih-normalized Γ (sym (eq-l-h Γ) ⟨ trans ⟩
                                                               ih             ⟨ trans ⟩
                                                               eq-r-h Γ )     ⟨ trans ⟩
                                              sym (eq-r-s Γ)))
-- Induction step failed
... | nothing = nothing

-- Prove a property with lemmas -----------------------------------------------
prove-with-lemmas : ℕ → List Lemma → (n : ℕ) (lhs rhs : Expr n) → Maybe (Equality lhs rhs)
prove-with-lemmas u lemmas (suc n) lhs rhs = induction u lemmas lhs rhs
prove-with-lemmas u lemmas zero    lhs rhs with normalize-with-correct lhs | normalize-with-correct rhs
... | lhs′ , eql | rhs′ , eqr = (λ x Γ → eql Γ ⟨ trans ⟩ x Γ ⟨ trans ⟩ sym (eqr Γ))
                                <$> simp u lemmas lhs′ rhs′


-- Prove a property without lemmas --------------------------------------------
prove : (n : ℕ) (lhs rhs : Expr n) → Maybe (Equality lhs rhs)
prove = prove-with-lemmas 0 []

-- Some examples --------------------------------------------------------------

-- Associativity of plus ------------------------------------------------------
-- This is how it looks if you use the vector
assoc-plus-vec : (Γ : Env 3) → lookup (# 0) Γ + (lookup (# 1) Γ + lookup (# 2) Γ)
                             ≡ (lookup (# 0) Γ + lookup (# 1) Γ) + lookup (# 2) Γ
assoc-plus-vec Γ = from-just (prove 3 (var (# 0) ⊕ (var (# 1) ⊕ var (# 2)))
                                      ((var (# 0) ⊕ (var (# 1))) ⊕ var (# 2))
                                      ) Γ

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

