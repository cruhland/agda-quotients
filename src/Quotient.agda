module Quotient where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

MultiArgFn :
  {ℓ : Level} (arity : ℕ) (argType : Set) (resultType : Set ℓ) → Set ℓ
MultiArgFn zero a r = r
MultiArgFn (suc n) a r = MultiArgFn n a (a → r)

Relation : (arity : ℕ) (A : Set) → Set₁
Relation arity A = MultiArgFn arity A Set

Rel₂ : (A : Set) → Set₁
Rel₂ A = Relation 2 A

data PairInt : Set where
  ⟨_-_⟩ : ℕ → ℕ → PairInt

≡PairInt : Rel₂ PairInt
≡PairInt ⟨ a - b ⟩ ⟨ c - d ⟩ = a + d ≡ b + c

Reflexive : {A : Set} (_≈_ : Rel₂ A) → Set
Reflexive _≈_ = ∀ x → x ≈ x

Symmetric : {A : Set} (_≈_ : Rel₂ A) → Set
Symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

Transitive : {A : Set} (_≈_ : Rel₂ A) → Set
Transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

record IsEquivalence {A : Set} (_≈_ : Rel₂ A) : Set where
  field
    reflexive : Reflexive _≈_
    symmetric : Symmetric _≈_
    transitive : Transitive _≈_

≡PairInt-refl : Reflexive ≡PairInt
≡PairInt-refl ⟨ a - b ⟩ = +-comm a b

≡PairInt-sym : Symmetric ≡PairInt
≡PairInt-sym ⟨ a - b ⟩ ⟨ c - d ⟩ a+d≡b+c rewrite +-comm a d | +-comm b c =
  sym a+d≡b+c

trans-lemma : (w x y z : ℕ) → (w + x) + (y + z) ≡ (w + z) + (x + y)
trans-lemma w x y z =
  solve 4 (λ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ⊜ (w ⊕ z) ⊕ (x ⊕ y)) refl w x y z

+-preserves-≡ : {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
+-preserves-≡ refl refl = refl

≡PairInt-trans : Transitive ≡PairInt
≡PairInt-trans ⟨ a - b ⟩ ⟨ c - d ⟩ ⟨ e - f ⟩ a-b≡c-d c-d≡e-f =
  let ≡-sum = +-preserves-≡ a-b≡c-d c-d≡e-f
      ≡-left = trans (trans-lemma a d c f) (cong ((a + f) +_) (+-comm d c))
      ≡-right = trans-lemma b c d e
      ≡-combined = trans (sym ≡-left) (trans ≡-sum ≡-right)
   in +-cancelʳ-≡ (a + f) (b + e) ≡-combined

≡PairInt-IsEquiv : IsEquivalence ≡PairInt
≡PairInt-IsEquiv =
  record
    { reflexive = ≡PairInt-refl
    ; symmetric = ≡PairInt-sym
    ; transitive = ≡PairInt-trans
    }

-- A setoid is a set A equipped with an equivalence relation _≈_
record Setoid : Set₁ where
  field
    A : Set
    _≈_ : Rel₂ A
    isEquiv : IsEquivalence _≈_

PairInt-Setoid : Setoid
PairInt-Setoid =
  record { A = PairInt ; _≈_ = ≡PairInt ; isEquiv = ≡PairInt-IsEquiv }
