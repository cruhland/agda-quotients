module Integer where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary.PropositionalEquality

data ℤ₃ : Set where
  ℤ₊ : ℕ → ℤ₃
  ℤ₀ : ℤ₃
  ℤ₋ : ℕ → ℤ₃

ℤ₊-injective : ∀ {m n} → ℤ₊ m ≡ ℤ₊ n → m ≡ n
ℤ₊-injective refl = refl

ℤ₋-injective : ∀ {m n} → ℤ₋ m ≡ ℤ₋ n → m ≡ n
ℤ₋-injective refl = refl

data ℕ² : Set where
  _─_ : ℕ → ℕ → ℕ²

ℕ²-≡₊ : ∀ {a₊ a₋ b₊ b₋} → (a₊ ─ a₋) ≡ (b₊ ─ b₋) → a₊ ≡ b₊
ℕ²-≡₊ refl = refl

ℕ²-≡₋ : ∀ {a₊ a₋ b₊ b₋} → (a₊ ─ a₋) ≡ (b₊ ─ b₋) → a₋ ≡ b₋
ℕ²-≡₋ refl = refl

toℕ² : ℤ₃ → ℕ²
toℕ² (ℤ₊ n) = suc n ─ zero
toℕ² ℤ₀ = zero ─ zero
toℕ² (ℤ₋ n) = zero ─ suc n

toℤ₃ : ℕ² → ℤ₃
toℤ₃ (zero ─ zero) = ℤ₀
toℤ₃ (zero ─ suc n₋) = ℤ₋ n₋
toℤ₃ (suc n₊ ─ zero) = ℤ₊ n₊
toℤ₃ (suc n₊ ─ suc n₋) = toℤ₃ (n₊ ─ n₋)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

ℕ≡? : (m n : ℕ) → Dec (m ≡ n)
ℕ≡? zero zero = yes refl
ℕ≡? zero (suc n) = no (λ ())
ℕ≡? (suc m) zero = no (λ ())
ℕ≡? (suc m) (suc n) with ℕ≡? m n
... | yes m≡n = yes (cong suc m≡n)
... | no ¬m≡n = no λ sm≡sn → ¬m≡n (suc-injective sm≡sn)

ℤ₃≡? : (a b : ℤ₃) → Dec (a ≡ b)
ℤ₃≡? (ℤ₊ m) (ℤ₊ n) with ℕ≡? m n
... | yes m≡n = yes (cong ℤ₊ m≡n)
... | no ¬m≡n = no λ ℤ₊m≡ℤ₊n → ¬m≡n (ℤ₊-injective ℤ₊m≡ℤ₊n)
ℤ₃≡? (ℤ₊ _) ℤ₀ = no (λ ())
ℤ₃≡? (ℤ₊ _) (ℤ₋ _) = no (λ ())
ℤ₃≡? ℤ₀ (ℤ₊ _) = no (λ ())
ℤ₃≡? ℤ₀ ℤ₀ = yes refl
ℤ₃≡? ℤ₀ (ℤ₋ _) = no (λ ())
ℤ₃≡? (ℤ₋ _) (ℤ₊ _) = no (λ ())
ℤ₃≡? (ℤ₋ _) ℤ₀ = no (λ ())
ℤ₃≡? (ℤ₋ m) (ℤ₋ n) with ℕ≡? m n
... | yes m≡n = yes (cong ℤ₋ m≡n)
... | no ¬m≡n = no λ ℤ₋m≡ℤ₋n → ¬m≡n (ℤ₋-injective ℤ₋m≡ℤ₋n)

ℕ²≡? : (a b : ℕ²) → Dec (a ≡ b)
ℕ²≡? (a₊ ─ a₋) (b₊ ─ b₋) with ℕ≡? a₊ b₊
ℕ²≡? (a₊ ─ a₋) (b₊ ─ b₋) | yes refl with ℕ≡? a₋ b₋
ℕ²≡? (a₊ ─ a₋) (b₊ ─ b₋) | yes refl | yes refl =
  yes refl
ℕ²≡? (a₊ ─ a₋) (b₊ ─ b₋) | yes refl | no ¬a₋≡b₋ =
  no (λ a≡b → ¬a₋≡b₋ (ℕ²-≡₋ a≡b))
ℕ²≡? (a₊ ─ a₋) (b₊ ─ b₋) | no ¬a₊≡b₊ =
  no λ a≡b → ¬a₊≡b₊ (ℕ²-≡₊ a≡b)

_≃_ : ℕ² → ℕ² → Set
(a₊ ─ a₋) ≃ (b₊ ─ b₋) = a₊ + b₋ ≡ a₋ + b₊

≃? : (a b : ℕ²) → Dec (a ≃ b)
≃? (a₊ ─ a₋) (b₊ ─ b₋) = ℕ≡? (a₊ + b₋) (a₋ + b₊)

_+₂_ : ℕ² → ℕ² → ℕ²
(a₊ ─ a₋) +₂ (b₊ ─ b₋) = (a₊ + b₊) ─ (a₋ + b₋)

{-
≃-cong : {A : Set} {a b : ℕ²} (f : ℕ² → ℕ²) → a ≃ b → f a ≃ f b
≃-cong f a≃b = {!!}
-}

drop-neg : ℕ² → ℕ²
drop-neg (a₊ ─ _) = (a₊ ─ zero)

3-5≃2-4 : (3 ─ 5) ≃ (2 ─ 4)
3-5≃2-4 = refl

_+₃_ : ℤ₃ → ℤ₃ → ℤ₃
a +₃ b = toℤ₃ (toℕ² a +₂ toℕ² b)
