<link rel="stylesheet" type="text/css" href="Agda.css">

# Quotient types in Agda

```agda
module Quotient where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Level hiding (lift) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

open ≡-Reasoning

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

record Prequotient : Set₁ where
  field S : Setoid
  open Setoid S public

  field
    Q : Set
    [_] : A → Q

  compat : {B : Set} → (f : A → B) → Set
  compat f = ∀ {x y} → x ≈ y → f x ≡ f y

  field
    sound : compat [_]

PairInt-refl-equiv : ∀ x → ≡PairInt ⟨ x - x ⟩ ⟨ zero - zero ⟩
PairInt-refl-equiv x = refl

PairInt-sum-left-equiv : ∀ a b → ≡PairInt ⟨ a - a + b ⟩ ⟨ zero - b ⟩
PairInt-sum-left-equiv a b rewrite +-comm (a + b) 0 = refl

data EnumInt : Set where
  ℤ₊ : ℕ → EnumInt
  ℤ₀ : EnumInt
  ℤ₋ : ℕ → EnumInt

PairInt→EnumInt : PairInt → EnumInt
PairInt→EnumInt ⟨ zero - zero ⟩ = ℤ₀
PairInt→EnumInt ⟨ zero - suc y ⟩ = ℤ₋ y
PairInt→EnumInt ⟨ suc x - zero ⟩ = ℤ₊ x
PairInt→EnumInt ⟨ suc x - suc y ⟩ = PairInt→EnumInt ⟨ x - y ⟩

PairInt→EnumInt-refl : ∀ x → PairInt→EnumInt ⟨ x - x ⟩ ≡ ℤ₀
PairInt→EnumInt-refl zero = refl
PairInt→EnumInt-refl (suc x) = PairInt→EnumInt-refl x

PairInt→EnumInt-right-sum : ∀ x y → PairInt→EnumInt ⟨ x - x + suc y ⟩ ≡ ℤ₋ y
PairInt→EnumInt-right-sum zero y = refl
PairInt→EnumInt-right-sum (suc x) y = PairInt→EnumInt-right-sum x y

PairInt→EnumInt-left-sum : ∀ x y → PairInt→EnumInt ⟨ suc x + y - y ⟩ ≡ ℤ₊ x
PairInt→EnumInt-left-sum x zero rewrite +-comm x 0 = refl
PairInt→EnumInt-left-sum x (suc y) rewrite +-suc x y =
  PairInt→EnumInt-left-sum x y

pi-ei-sound :
  (a b : PairInt) → ≡PairInt a b → PairInt→EnumInt a ≡ PairInt→EnumInt b
pi-ei-sound ⟨ zero - zero ⟩ ⟨ c - d ⟩ a+d≡b+c
  rewrite a+d≡b+c | PairInt→EnumInt-refl c = refl
pi-ei-sound ⟨ zero - suc b ⟩ ⟨ c - d ⟩ a+d≡b+c
  rewrite +-comm (suc b) c | a+d≡b+c | PairInt→EnumInt-right-sum c b = refl
pi-ei-sound ⟨ suc a - zero ⟩ ⟨ c - d ⟩ a+d≡b+c rewrite sym a+d≡b+c =
  sym (PairInt→EnumInt-left-sum a d)
pi-ei-sound ⟨ suc a - suc b ⟩ ⟨ c - d ⟩ a+d≡b+c =
  pi-ei-sound ⟨ a - b ⟩ ⟨ c - d ⟩ (suc-injective a+d≡b+c)

PairInt-EnumInt-Prequotient : Prequotient
PairInt-EnumInt-Prequotient =
  record
    { S = PairInt-Setoid
    ; Q = EnumInt
    ; [_] = PairInt→EnumInt
    ; sound = λ {x y} → pi-ei-sound x y
    }

module _ {PQ : Prequotient} where
  open Prequotient PQ

  compat₂ : {B : Q → Set} → (f : (a : A) → B [ a ]) → Set
  compat₂ {B} f = ∀ {x y} → (r : x ≈ y) → subst B (sound r) (f x) ≡ f y

record Quotient : Set₁ where
  field PQ : Prequotient
  open Prequotient PQ public
  field
    qelim :
      (B : Q → Set) →
      (f : (a : A) → B [ a ]) →
      compat₂ {PQ} {B} f →
      (q : Q) →
      B q
    qelim-β : ∀ B f → (c : compat₂ {PQ} f) → ∀ a → qelim B f c [ a ] ≡ f a

record ExactQuotient : Set₁ where
  field QQ : Quotient
  open Quotient QQ public
  field
    exact : ∀ {x y} → [ x ] ≡ [ y ] → x ≈ y

record AltQuotient : Set₁ where
  field PQ : Prequotient
  open Prequotient PQ public
  field
    lift : {B : Set} (f : A → B) → compat f → Q → B
    lift-β : ∀ {B} f x → (A≈→B≡ : compat f) → lift {B} f A≈→B≡ [ x ] ≡ f x
    qind : (C : Q → Set) → (∀ x → C [ x ]) → (q : Q) → C q

cong-Σ :
  {A : Set} {B : A → Set} {a a′ : A} {b : B a} {b′ : B a′} →
  (p : a ≡ a′) →
  subst B p b ≡ b′ →
  (a , b) ≡ (a′ , b′)
cong-Σ refl refl = refl

proj₁-≡ :
  {A : Set} {B : A → Set} {p₁ p₂ : Σ A B} → p₁ ≡ p₂ → proj₁ p₁ ≡ proj₁ p₂
proj₁-≡ refl = refl

proj₂-≡ :
  {A : Set} {B : A → Set} {p₁ p₂ : Σ A B} →
  (eq : p₁ ≡ p₂) →
  subst B (proj₁-≡ eq) (proj₂ p₁) ≡ proj₂ p₂
proj₂-≡ refl = refl

≡-irr : {A : Set} {a a′ : A} (eq₁ eq₂ : a ≡ a′) → eq₁ ≡ eq₂
≡-irr refl refl = refl

subst-irr :
  {A : Set} {B : A → Set} {a a′ : A} {b : B a} (eq₁ eq₂ : a ≡ a′) →
  subst B eq₁ b ≡ subst B eq₂ b
subst-irr eq₁ eq₂ rewrite ≡-irr eq₁ eq₂ = refl

module _ (AQ : AltQuotient) where
  open AltQuotient AQ using (PQ; lift; lift-β; qind)
  open Prequotient PQ

  module _ (P : Q → Set) (p : (x : A) → P [ x ]) (A≈→P≡ : compat₂ {PQ} p) where
    U : Set
    U = Σ Q P

    p′ : A → U
    p′ x′ = [ x′ ] , p x′

    compat-p′ : compat p′
    compat-p′ x≈y = cong-Σ (sound x≈y) (A≈→P≡ x≈y)

    liftU : Q → U
    liftU = lift p′ compat-p′

    liftU-β : ∀ x → liftU [ x ] ≡ p′ x
    liftU-β x = lift-β p′ x compat-p′

    proj₁-liftU-id : Q → Set
    proj₁-liftU-id c = proj₁ (liftU c) ≡ c

    proj₁U→Q : (c : Q) → proj₁-liftU-id c
    proj₁U→Q = qind proj₁-liftU-id λ x → cong proj₁ (liftU-β x)

    qelim₁ : (c : Q) → P c
    qelim₁ c = subst P (proj₁U→Q c) (proj₂ (liftU c))

    proj₁-liftU-β : ∀ x → proj₁ (liftU [ x ]) ≡ proj₁ (p′ x)
    proj₁-liftU-β x = proj₁-≡ (liftU-β x)

    proj₂-liftU-β :
      ∀ x → subst P (proj₁-liftU-β x) (proj₂ (liftU [ x ])) ≡ proj₂ (p′ x)
    proj₂-liftU-β x = proj₂-≡ (liftU-β x)

    qelim-β₁ : ∀ x → qelim₁ [ x ] ≡ p x
    qelim-β₁ x =
      begin
        qelim₁ [ x ]
      ≡⟨⟩
        subst P (proj₁U→Q [ x ]) (proj₂ (liftU [ x ]))
      ≡⟨ subst-irr (proj₁U→Q [ x ]) (proj₁-liftU-β x) ⟩
        subst P (proj₁-liftU-β x) (proj₂ (liftU [ x ]))
      ≡⟨ proj₂-liftU-β x ⟩
        proj₂ (p′ x)
      ≡⟨⟩
        p x
      ∎

AltQuotient→Quotient : AltQuotient → Quotient
AltQuotient→Quotient AQ =
  record { PQ = AltQuotient.PQ AQ ; qelim = qelim₁ AQ ; qelim-β = qelim-β₁ AQ }
```

