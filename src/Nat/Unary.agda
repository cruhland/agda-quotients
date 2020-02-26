module Nat.Unary where

open import Data.Sum
open import Function
open import Nat.Class
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data ℕ₁ : Set where
  zero : ℕ₁
  succ : ℕ₁ → ℕ₁

ind : (P : ℕ₁ → Set) → P zero → (∀ {k} → P k → P (succ k)) → ∀ n → P n
ind P z s zero = z
ind P z s (succ n) = ind (P ∘ succ) (s z) (λ {k} → s {succ k}) n

ind′ : (P : ℕ₁ → Set) → P zero → (∀ {k} → P k → P (succ k)) → ∀ n → P n
ind′ P z s zero = z
ind′ P z s (succ n) = s (ind′ P z s n)

rec : {A : Set} → A → (A → A) → ℕ₁ → A
rec {A} z s n = ind (const A) z (λ {_} → s) n

rec-succ : ∀ {A} z (s : A → A) n → rec (s z) s n ≡ s (rec z s n)
rec-succ z s zero = refl
rec-succ z s (succ n) =
  begin
    rec (s z) s (succ n)
  ≡⟨⟩
    rec (s (s z)) s n
  ≡⟨ rec-succ (s z) s n ⟩
    s (rec (s z) s n)
  ≡⟨⟩
    s (rec z s (succ n))
  ∎

data _<_ : ℕ₁ → ℕ₁ → Set where
  z<s : ∀ {n} → zero < succ n
  s<s : ∀ {m n} → m < n → succ m < succ n

n<sn : ∀ {n} → n < succ n
n<sn {zero} = z<s
n<sn {succ n} = s<s n<sn

tighten : ∀ {m n} → m < succ n → m < n ⊎ m ≡ n
tighten {zero} {zero} z<s = inj₂ refl
tighten {zero} {succ n′} z<s = inj₁ z<s
tighten {succ m′} {succ n′} (s<s m′<sn′) with tighten m′<sn′
tighten {succ m′} {succ n′} (s<s m′<sn′) | inj₁ m′<n′ = inj₁ (s<s m′<n′)
tighten {succ m′} {succ n′} (s<s m′<sn′) | inj₂ m′≡n′ = inj₂ (cong succ m′≡n′)

SIndHyp : (ℕ₁ → Set) → ℕ₁ → Set
SIndHyp P n = ∀ {m} → m < n → P m

sind : (P : ℕ₁ → Set) → (∀ {k} → SIndHyp P k → P k) → ∀ n → P n
sind P h n = prf (succ n) {n} n<sn
  where
    lem : {p : ℕ₁} (hp : SIndHyp P p) → SIndHyp P (succ p)
    lem hp m<sp with tighten m<sp
    lem hp m<sp | inj₁ m<p = hp m<p
    lem hp m<sp | inj₂ refl = h hp

    prf : ∀ n → SIndHyp P n
    prf = ind (SIndHyp P) (λ ()) lem

_+_ : ℕ₁ → ℕ₁ → ℕ₁
m + n = rec n succ m

+-zero : ∀ {n} → zero + n ≡ n
+-zero = refl

+-succ : ∀ {m n} → succ m + n ≡ m + succ n
+-succ = refl

instance
  Nat-ℕ₁ : Nat ℕ₁
  Nat-ℕ₁ = record
    { zero = zero
    ; succ = succ
    ; ind = ind
    ; _+_ = _+_
    ; +-zero = +-zero
    ; +-succ = λ {m n} → +-succ {m} {n}
    }
