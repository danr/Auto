module Polynomials where

open import Data.Nat

data Reg : ℕ → Set where
  var      : ∀ {n} → Reg (suc n)
  wk       : ∀ {n} → (t : Reg n) → Reg (suc n)
  zero one : ∀ {n} → Reg n
  _⨁_ _⨂_ : ∀ {n} → (s t : Reg n) → Reg n
  fix      : ∀ {n} → (f : Reg (suc n)) → Reg n

data Tel : ℕ → Set where
  ε   : Tel zero
  _▷_ : ∀ {n} → (ts : Tel n) (t : Reg n) → Tel (suc n)
--_▶_ : ∀ {n} → (ts : Tel n) (t : set)   → Tel (suc n)

data ⟦_⟧ : ∀ {n} → Reg n → Tel n → Set where
  top  : ∀ {n} {t : Reg n} {Γ : Tel n}   → ⟦ t ⟧ Γ → ⟦ var ⟧ (Γ ▷ t)
--ty   : ∀ {n} {t : set}   {Γ : Tel n}   → t       → ⟦ var ⟧ (Γ ▶ t)
  pop  : ∀ {n} {s t : Reg n} {Γ : Tel n} → ⟦ t ⟧ Γ → ⟦ wk t ⟧ (Γ ▷ s)
  inl  : ∀ {n} {s t : Reg n} {Γ : Tel n} → ⟦ s ⟧ Γ → ⟦ s ⨁ t ⟧ Γ
  inr  : ∀ {n} {s t : Reg n} {Γ : Tel n} → ⟦ t ⟧ Γ → ⟦ s ⨁ t ⟧ Γ
  void : ∀ {n} {Γ : Tel n}               → ⟦ one ⟧ Γ
  pair : ∀ {n} {s t : Reg n} {Γ : Tel n} → ⟦ s ⟧ Γ → ⟦ t ⟧ Γ → ⟦ s ⨂ t ⟧ Γ
  inj  : ∀ {n} {f : Reg (suc n)} {Γ : Tel n} → ⟦ f ⟧ (Γ ▷ fix f) → ⟦ fix f ⟧ Γ

Nat : ∀ {n} → Reg n
Nat = fix (one ⨁ var)

z : ∀ {n} {Γ : Tel n} → ⟦ Nat ⟧ Γ
z = inj (inl void)

s : ∀ {n} {Γ : Tel n} → ⟦ Nat ⟧ Γ → ⟦ Nat ⟧ Γ
s n = inj (inr (top n))

plus : ∀ {n} {Γ : Tel n} → ⟦ Nat ⟧ Γ → ⟦ Nat ⟧ Γ → ⟦ Nat ⟧ Γ
plus (inj (inl void))    n = n
plus (inj (inr (top m))) n = s (plus m n)

List : ∀ {n} → Reg (suc n)
List = fix (one ⨁ (wk var ⨂ var))

nil : ∀ {n} {Γ : Tel (suc n)} → ⟦ List ⟧ Γ
nil = inj (inl void)

cons : ∀ {n} {Γ : Tel (suc n)} → ⟦ var ⟧ Γ → ⟦ List ⟧ Γ → ⟦ List ⟧ Γ
cons a as = inj (inr (pair (pop a) (top as)))

append : ∀ {n} {Γ : Tel (suc n)} → ⟦ List ⟧ Γ → ⟦ List ⟧ Γ → ⟦ List ⟧ Γ
append (inj (inl void))                    bs = bs
append (inj (inr (pair (pop a) (top as)))) bs = cons a (append as bs)

Nat→ℕ : ∀ {n} (Γ : Tel n) → ⟦ Nat ⟧ Γ → ℕ
Nat→ℕ _ (inj (inl void))    = zero
Nat→ℕ _ (inj (inr (top n))) = suc (Nat→ℕ _ n)

ℕ→Nat : ∀ {n} {Γ : Tel n} → ℕ → ⟦ Nat ⟧ Γ
ℕ→Nat zero    = inj (inl void)
ℕ→Nat (suc n) = inj (inr (top (ℕ→Nat n)))

open import Relation.Binary.PropositionalEquality

Nat-ok : ∀ {n} {Γ : Tel n} (x : ℕ) → Nat→ℕ Γ (ℕ→Nat x) ≡ x
Nat-ok zero    = refl
Nat-ok (suc x) = cong suc (Nat-ok x)

plus-ok : ∀ {n} {Γ : Tel n} (x y : ℕ) → Nat→ℕ Γ (plus (ℕ→Nat x) (ℕ→Nat y)) ≡ x + y
plus-ok zero    y = Nat-ok y
plus-ok (suc x) y = cong suc (plus-ok x y)

