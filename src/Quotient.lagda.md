<link rel="stylesheet" type="text/css" href="Agda.css">

# Quotient types in Agda

This article attempts to explain how quotient types work in Agda. The
code is adapted from the paper [Definable Quotients in Type
Theory](http://www.cs.nott.ac.uk/~psztxa/publ/defquotients.pdf) by
Altenkirch, Anberrée, and Li.

We start with the module declaration and imports, as required by Agda:

```agda
module Quotient where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Level hiding (lift) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

open ≡-Reasoning
```

Don't worry too much about why these specific imports are needed; I'll
refer back to them when they're actually referenced in what follows.

So, what is a quotient type? Frequently when modeling a concept in
Agda, there are multiple data types that do the job, but one may be
better to use than another in certain contexts. In particular, one
representation may exactly capture the elements of the domain, such
that propositional equality on the data type corresponds with the
notion of equality for the concept being modeled; while another
representation may be easier to work with, but at the cost of having
redundant elements which prevent the meaningful usage of
equality. Quotient types (or just _quotients_ for short) allow us to
convert between the two representations and use the one that's most
convenient for the task at hand.

A specific example will help illustrate. Suppose we'd like to model
the integers as an Agda data type. In our first attempt, we want
propositional equality over the data type to correspond with actual
equality between integers, so we'd write something like this:

```agda
data ℤ₁ : Set where
  ℤ₊ : ℕ → ℤ₁
  ℤ₀ : ℤ₁
  ℤ₋ : ℕ → ℤ₁
```

This representation relies on ℕ's propositional equality to ensure
that there is exactly one term of `ℤ₁` for each integer (hence
justifying the subscript `1`). The constructors `ℤ₊` and `ℤ₋`
represent the positive and negative integers, respectively, and accept
as argument the predecessor of the corresponding natural number; for
example, -3 is represented as `ℤ₋ (suc (suc zero))`.

We could have used a similar representation with only two constructors
(representing the nonnegative integers and strictly negative
integers), but the symmetry of the above definition is conceptually
clearer. Unfortunately this clarity doesn't extend to functions defined over this data type. Consider addition:

```agda
_+₁_ : ℤ₁ → ℤ₁ → ℤ₁
ℤ₊ n₊ +₁ ℤ₊ m₊ = ℤ₊ (suc (n₊ + m₊))
ℤ₊ n₊ +₁ ℤ₀ = ℤ₊ n₊
ℤ₊ zero +₁ ℤ₋ zero = ℤ₀
ℤ₊ zero +₁ ℤ₋ (suc m₋) = ℤ₋ m₋
ℤ₊ (suc n₊) +₁ ℤ₋ zero = ℤ₊ n₊
ℤ₊ (suc n₊) +₁ ℤ₋ (suc m₋) = (ℤ₊ n₊) +₁ (ℤ₋ m₋)
ℤ₀ +₁ y = y
ℤ₋ n₋ +₁ ℤ₋ m₋ = ℤ₋ (suc (n₋ + m₋))
ℤ₋ n₋ +₁ ℤ₀ = ℤ₋ n₋
ℤ₋ zero +₁ ℤ₊ zero = ℤ₀
ℤ₋ zero +₁ ℤ₊ (suc m₊) = ℤ₊ m₊
ℤ₋ (suc n₋) +₁ ℤ₊ zero = ℤ₋ n₋
ℤ₋ (suc n₋) +₁ ℤ₊ (suc m₊) = (ℤ₋ n₋) +₁ (ℤ₊ m₊)
```

What a mess! It's hard to tell whether this implementation is
correct. And trying to prove correctness or other properties of this
function would be a nightmare with all the cases that would need to be
considered. Do we just have to grit our teeth and slog through it?

No! If we pick a different representation, defining integer addition
is a breeze:

```agda
data ℤ₂ : Set where
  ⟨_-_⟩ : ℕ → ℕ → ℤ₂

_+₂_ : ℤ₂ → ℤ₂ → ℤ₂
⟨ n₁ - n₂ ⟩ +₂ ⟨ m₁ - m₂ ⟩ = ⟨ n₁ + m₁ - n₂ + m₂ ⟩
```

By denoting an integer as the difference of two natural numbers, `ℤ₂`
is much easier to work with. For example, the definition of `_+₂_` is
an easy consequence of the rules of algebra! But it comes at a cost:
there are many terms that are not propositionally equal that still
represent the same integer (e.g. `⟨ 3 - 5 ⟩`, `⟨ 2 - 4 ⟩`, and `⟨ 0 -
2 ⟩` all denote -2). Do we just have to give up on using the `_≡_`
relation on elements of `ℤ₂`?

```agda
MultiArgFn :
  {ℓ : Level} (arity : ℕ) (argType : Set) (resultType : Set ℓ) → Set ℓ
MultiArgFn zero a r = r
MultiArgFn (suc n) a r = MultiArgFn n a (a → r)

Relation : (arity : ℕ) (A : Set) → Set₁
Relation arity A = MultiArgFn arity A Set

Rel₂ : (A : Set) → Set₁
Rel₂ A = Relation 2 A

≡ℤ₂ : Rel₂ ℤ₂
≡ℤ₂ ⟨ a - b ⟩ ⟨ c - d ⟩ = a + d ≡ b + c

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

≡ℤ₂-refl : Reflexive ≡ℤ₂
≡ℤ₂-refl ⟨ a - b ⟩ = +-comm a b

≡ℤ₂-sym : Symmetric ≡ℤ₂
≡ℤ₂-sym ⟨ a - b ⟩ ⟨ c - d ⟩ a+d≡b+c rewrite +-comm a d | +-comm b c =
  sym a+d≡b+c

trans-lemma : (w x y z : ℕ) → (w + x) + (y + z) ≡ (w + z) + (x + y)
trans-lemma w x y z =
  solve 4 (λ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ⊜ (w ⊕ z) ⊕ (x ⊕ y)) refl w x y z

+-preserves-≡ : {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
+-preserves-≡ refl refl = refl

≡ℤ₂-trans : Transitive ≡ℤ₂
≡ℤ₂-trans ⟨ a - b ⟩ ⟨ c - d ⟩ ⟨ e - f ⟩ a-b≡c-d c-d≡e-f =
  let ≡-sum = +-preserves-≡ a-b≡c-d c-d≡e-f
      ≡-left = trans (trans-lemma a d c f) (cong ((a + f) +_) (+-comm d c))
      ≡-right = trans-lemma b c d e
      ≡-combined = trans (sym ≡-left) (trans ≡-sum ≡-right)
   in +-cancelʳ-≡ (a + f) (b + e) ≡-combined

≡ℤ₂-IsEquiv : IsEquivalence ≡ℤ₂
≡ℤ₂-IsEquiv =
  record
    { reflexive = ≡ℤ₂-refl
    ; symmetric = ≡ℤ₂-sym
    ; transitive = ≡ℤ₂-trans
    }

-- A setoid is a set A equipped with an equivalence relation _≈_
record Setoid : Set₁ where
  field
    A : Set
    _≈_ : Rel₂ A
    isEquiv : IsEquivalence _≈_

ℤ₂-Setoid : Setoid
ℤ₂-Setoid =
  record { A = ℤ₂ ; _≈_ = ≡ℤ₂ ; isEquiv = ≡ℤ₂-IsEquiv }

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

ℤ₂-refl-equiv : ∀ x → ≡ℤ₂ ⟨ x - x ⟩ ⟨ zero - zero ⟩
ℤ₂-refl-equiv x = refl

ℤ₂-sum-left-equiv : ∀ a b → ≡ℤ₂ ⟨ a - a + b ⟩ ⟨ zero - b ⟩
ℤ₂-sum-left-equiv a b rewrite +-comm (a + b) 0 = refl

ℤ₂→ℤ₁ : ℤ₂ → ℤ₁
ℤ₂→ℤ₁ ⟨ zero - zero ⟩ = ℤ₀
ℤ₂→ℤ₁ ⟨ zero - suc y ⟩ = ℤ₋ y
ℤ₂→ℤ₁ ⟨ suc x - zero ⟩ = ℤ₊ x
ℤ₂→ℤ₁ ⟨ suc x - suc y ⟩ = ℤ₂→ℤ₁ ⟨ x - y ⟩

ℤ₂→ℤ₁-refl : ∀ x → ℤ₂→ℤ₁ ⟨ x - x ⟩ ≡ ℤ₀
ℤ₂→ℤ₁-refl zero = refl
ℤ₂→ℤ₁-refl (suc x) = ℤ₂→ℤ₁-refl x

ℤ₂→ℤ₁-right-sum : ∀ x y → ℤ₂→ℤ₁ ⟨ x - x + suc y ⟩ ≡ ℤ₋ y
ℤ₂→ℤ₁-right-sum zero y = refl
ℤ₂→ℤ₁-right-sum (suc x) y = ℤ₂→ℤ₁-right-sum x y

ℤ₂→ℤ₁-left-sum : ∀ x y → ℤ₂→ℤ₁ ⟨ suc x + y - y ⟩ ≡ ℤ₊ x
ℤ₂→ℤ₁-left-sum x zero rewrite +-comm x 0 = refl
ℤ₂→ℤ₁-left-sum x (suc y) rewrite +-suc x y =
  ℤ₂→ℤ₁-left-sum x y

pi-ei-sound :
  (a b : ℤ₂) → ≡ℤ₂ a b → ℤ₂→ℤ₁ a ≡ ℤ₂→ℤ₁ b
pi-ei-sound ⟨ zero - zero ⟩ ⟨ c - d ⟩ a+d≡b+c
  rewrite a+d≡b+c | ℤ₂→ℤ₁-refl c = refl
pi-ei-sound ⟨ zero - suc b ⟩ ⟨ c - d ⟩ a+d≡b+c
  rewrite +-comm (suc b) c | a+d≡b+c | ℤ₂→ℤ₁-right-sum c b = refl
pi-ei-sound ⟨ suc a - zero ⟩ ⟨ c - d ⟩ a+d≡b+c rewrite sym a+d≡b+c =
  sym (ℤ₂→ℤ₁-left-sum a d)
pi-ei-sound ⟨ suc a - suc b ⟩ ⟨ c - d ⟩ a+d≡b+c =
  pi-ei-sound ⟨ a - b ⟩ ⟨ c - d ⟩ (suc-injective a+d≡b+c)

ℤ₂-ℤ₁-Prequotient : Prequotient
ℤ₂-ℤ₁-Prequotient =
  record
    { S = ℤ₂-Setoid
    ; Q = ℤ₁
    ; [_] = ℤ₂→ℤ₁
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

## Further reading

Here are some sources that helped me out while I was writing this:

1. [Equivalence
   class](https://en.wikipedia.org/wiki/Equivalence_class), Wikipedia.
1. [Quotient Types for Programmers](https://www.hedonisticlearning.com/posts/quotient-types-for-programmers.html), by Derek Elkins.
