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

## Introduction

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
that there is exactly one term of `ℤ₁` for each integer. The
constructors `ℤ₊` and `ℤ₋` represent the positive and negative
integers, respectively, and accept as argument the predecessor of the
corresponding natural number; for example, -3 is represented as `ℤ₋
(suc (suc zero))`.

We could have used a similar representation with only two constructors
(representing the nonnegative integers and strictly negative
integers), but the symmetry of the above definition is conceptually
clearer. Unfortunately this clarity doesn't extend to functions defined over this data type. Consider addition:

```agda
_+₁-bad_ : ℤ₁ → ℤ₁ → ℤ₁
ℤ₊ a₊ +₁-bad ℤ₊ b₊ = ℤ₊ (suc (a₊ + b₊))
ℤ₊ a₊ +₁-bad ℤ₀ = ℤ₊ a₊
ℤ₊ zero +₁-bad ℤ₋ zero = ℤ₀
ℤ₊ zero +₁-bad ℤ₋ (suc b₋) = ℤ₋ b₋
ℤ₊ (suc a₊) +₁-bad ℤ₋ zero = ℤ₊ a₊
ℤ₊ (suc a₊) +₁-bad ℤ₋ (suc b₋) = (ℤ₊ a₊) +₁-bad (ℤ₋ b₋)
ℤ₀ +₁-bad y = y
ℤ₋ a₋ +₁-bad ℤ₋ b₋ = ℤ₋ (suc (a₋ + b₋))
ℤ₋ a₋ +₁-bad ℤ₀ = ℤ₋ a₋
ℤ₋ zero +₁-bad ℤ₊ zero = ℤ₀
ℤ₋ zero +₁-bad ℤ₊ (suc b₊) = ℤ₊ b₊
ℤ₋ (suc a₋) +₁-bad ℤ₊ zero = ℤ₋ a₋
ℤ₋ (suc a₋) +₁-bad ℤ₊ (suc b₊) = (ℤ₋ a₋) +₁-bad (ℤ₊ b₊)
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
⟨ a₁ - a₂ ⟩ +₂ ⟨ b₁ - b₂ ⟩ = ⟨ a₁ + b₁ - a₂ + b₂ ⟩
```

By denoting an integer as the difference of two natural numbers, `ℤ₂`
is much easier to work with. For example, the definition of `_+₂_` is
an easy consequence of the rules of algebra! But it comes at a cost:
there are many terms that are not propositionally equal that still
represent the same integer (e.g. `⟨ 2 - 5 ⟩`, `⟨ 1 - 4 ⟩`, and `⟨ 0 -
3 ⟩` all denote -3). Do we just have to give up on using the `_≡_`
relation on elements of `ℤ₂`?

Well, technically yes, but for practical purposes no. We can use `ℤ₂`
for writing functions and proving properties, and `ℤ₁` for comparisons
and enumeration, with a quotient construction. The main idea is to
map, or label, each `ℤ₂` value with the unique `ℤ₁` value that denotes
the same integer. A more mathematical way to phrase it would be that
we're partitioning `ℤ₂` into [_equivalence
classes_](https://en.wikipedia.org/wiki/Equivalence_class), with each
class having a canonical representative in `ℤ₁`.

## Equivalence relations

As a first step, we have to define what it means for two `ℤ₂` terms to
represent the same integer, that is, we need an [_equivalence
relation_](https://en.wikipedia.org/wiki/Equivalence_relation). The
first sentence of that Wikipedia page describes exacatly what is
needed: "an equivalence relation is a binary relation that is
reflexive, symmetric and transitive". Let's formalize that in Agda!

```agda
Rel₂ : (A : Set) → Set₁
Rel₂ A = A → A → Set

Reflexive : {A : Set} (_∼_ : Rel₂ A) → Set
Reflexive _∼_ = ∀ {x} → x ∼ x

Symmetric : {A : Set} (_∼_ : Rel₂ A) → Set
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

Transitive : {A : Set} (_∼_ : Rel₂ A) → Set
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

record IsEquivalence {A : Set} (_≈_ : Rel₂ A) : Set where
  field
    reflexive : Reflexive _≈_
    symmetric : Symmetric _≈_
    transitive : Transitive _≈_
```

We first create a shorthand `Rel₂` for binary relations on a set `A`,
since we'll need to refer to them in the subsequent definitions. Next,
we define the properties that an equivalence relation must satisfy:

1. reflexivity: all elements are equivalent to themselves;
1. symmetry: equivalence is mutual, like friendship (it goes both
   ways);
1. transitivity: equivalence is "viral", like the property of being
   related to a person (elements that are equivalent to some element
   are equivalent to each other).

Finally we package the properties up into a convenient record type
that captures exactly what it means for some arbitrary binary relation
`_≈_` to be an equivalence relation. All of these definitions can be
found in the Agda standard library; I didn't use them here because
they are more general and therefore harder to explain. But please
click on the imports below if you're interested in learning more.

```agda
module _ where
  import Relation.Binary
    using (Reflexive; Symmetric; Transitive; IsEquivalence)
```

Now that we've precisely specified what an equivalence relation is, we
should try to find one for `ℤ₂` that makes all terms that represent
the same integer equivalent to each other. In mathematical terms, if
we have integers `a = ⟨ a₁ - a₂ ⟩` and `b = ⟨ b₁ - b₂ ⟩`, then `a = b`
if and only if (iff) `a₁ - a₂ = b₁ - b₂`. Adding `a₂` and `b₂` to both
sides to eliminate the subtractions gives us `a₁ + b₂ = a₂ + b₁`,
which only requires natural number addition. Eureka!

```agda
_≈₂_ : Rel₂ ℤ₂
⟨ a₁ - a₂ ⟩ ≈₂ ⟨ b₁ - b₂ ⟩ = a₁ + b₂ ≡ a₂ + b₁
```

Now we need to show that `_≈₂_` is an equivalence relation, i.e. we
need to construct a value of type `IsEquivalence _≈₂_`. Let's start
with the first and simplest property, reflexivity:

```agda
≈₂-refl : Reflexive _≈₂_
≈₂-refl {⟨ a₁ - a₂ ⟩} = +-comm a₁ a₂
```

Expanding the definition of `Reflexive`, and pattern matching on the
lone `ℤ₂` argument, we see that we need to prove `⟨ a₁ - a₂ ⟩ ≈₂ ⟨ a₁
- a₂ ⟩`. Evaluating `_≈₂_`, we can see this is the same as `a₁ + a₂ ≡
a₂ + a₁`, which is just the commutative property of `+` on `ℕ`.

Symmetry is slightly more involved:

```agda
≈₂-sym : Symmetric _≈₂_
≈₂-sym {⟨ a₁ - a₂ ⟩} {⟨ b₁ - b₂ ⟩} a₁+b₂≡a₂+b₁ =
  begin
    b₁ + a₂
  ≡⟨ +-comm b₁ a₂ ⟩
    a₂ + b₁
  ≡⟨ sym a₁+b₂≡a₂+b₁ ⟩
    a₁ + b₂
  ≡⟨ +-comm a₁ b₂ ⟩
    b₂ + a₁
  ∎
```

To prove symmetry, we're given that `a ≈₂ b` and have to show that `b
≈₂ a`. After expanding the definitions of `a`, `b`, and `_≈₂_`, this
means that given `a₁ + b₂ ≡ a₂ + b₁`, we have to show that `b₁ + a₂ ≡
b₂ + a₁`. The result follows from commutativity.

Transitivity turns out to be way more difficult, and requires some
lemmas to simplify the main proof. Here's the whole thing; see below
for an English translation:

```agda
≈₂-trans : Transitive _≈₂_
≈₂-trans {⟨ a₁ - a₂ ⟩} {⟨ b₁ - b₂ ⟩} {⟨ c₁ - c₂ ⟩} a₁+b₂≡a₂+b₁ b₁+c₂≡b₂+c₁ =
  let [a₁+b₂]+[b₁+c₂]≡[a₂+b₁]+[b₂+c₁] = eqn-add a₁+b₂≡a₂+b₁ b₁+c₂≡b₂+c₁
      [a₁+c₂]+[b₂+b₁]≡[a₂+c₁]+[b₁+b₂] = rearr [a₁+b₂]+[b₁+c₂]≡[a₂+b₁]+[b₂+c₁]
      a₁+c₂≡a₂+c₁ = cancelʳ [a₁+c₂]+[b₂+b₁]≡[a₂+c₁]+[b₁+b₂] (+-comm b₂ b₁)
   in a₁+c₂≡a₂+c₁
  where
    eqn-add : ∀ {m n p q} → m ≡ n → p ≡ q → m + p ≡ n + q
    eqn-add refl refl = refl

    cancelʳ : ∀ {m n p q} → m + p ≡ n + q → p ≡ q → m ≡ n
    cancelʳ {m} {n} sum-eq refl = +-cancelʳ-≡ m n sum-eq

    out-left-in-right :
      ∀ {m₁ m₂ n₁ n₂} → (m₁ + n₁) + (n₂ + m₂) ≡ (m₁ + m₂) + (n₁ + n₂)
    out-left-in-right {m₁} {m₂} {n₁} {n₂} =
      let eqn = λ m₁ m₂ n₁ n₂ → (m₁ ⊕ n₁) ⊕ (n₂ ⊕ m₂) ⊜ (m₁ ⊕ m₂) ⊕ (n₁ ⊕ n₂)
       in solve 4 eqn refl m₁ m₂ n₁ n₂

    rearr :
      (a₁ + b₂) + (b₁ + c₂) ≡ (a₂ + b₁) + (b₂ + c₁) →
      (a₁ + c₂) + (b₂ + b₁) ≡ (a₂ + c₁) + (b₁ + b₂)
    rearr [a₁+b₂]+[b₁+c₂]≡[a₂+b₁]+[b₂+c₁] =
      begin
        (a₁ + c₂) + (b₂ + b₁)
      ≡⟨ sym (out-left-in-right {a₁}) ⟩
        (a₁ + b₂) + (b₁ + c₂)
      ≡⟨ [a₁+b₂]+[b₁+c₂]≡[a₂+b₁]+[b₂+c₁] ⟩
        (a₂ + b₁) + (b₂ + c₁)
      ≡⟨ out-left-in-right {a₂} ⟩
        (a₂ + c₁) + (b₁ + b₂)
      ∎
```

Despite all the text required to show it, the reasoning behind this
proof is straightforward; it's just algebra. As with the proofs of
reflexivity and symmetry, we start with some integers and relations
between them: `a`, `b`, and `c`, where `a ≈₂ b` and `b ≈₂ c`. We have
to show that `a ≈₂ c`. After pattern matching, we name the equivalence
conditions after their underlying equalities, and our goal is now to
show that `a₁ + c₂ ≡ a₂ + c₁`.

Looking at the equality arguments to the proof, we see that `a₁` and
`c₂` each only occur once, and are on the left-hand side of their
respective equalities; similarly, `a₂` and `c₁` each only occur once,
but on the right-hand side. Since our goal requires we sum both of
those pairs, let's just add the two equations together! That produces
the result of the first line of the proof.

The next two lines are simple algebra. We rearrange terms to group `a`
and `c` components separately from `b` components. Now the rightmost
part of each side of the equation is the same value, `b₁ + b₂` (taking
commutativity into account); thus we can cancel it out and obtain our
goal.

The lemmas are self-explanatory, except for `out-left-in-right`;
there, we used an algebra solver to avoid a bunch of tedious rewrites
involving associativity and commutativity. We imported the solver at
the top of the file, specifying that we wanted to use the commutative
monoid of addition with identity element zero, since we're only
dealing with sums of natural numbers here:

```agda
module _ where
  open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid
```

Whew! That's all the proofs; now just glue them together:

```agda
≈₂-IsEquiv : IsEquivalence _≈₂_
≈₂-IsEquiv =
  record { reflexive = ≈₂-refl ; symmetric = ≈₂-sym ; transitive = ≈₂-trans }
```

Voilà! We've demonstrated that `ℤ₂` can be divided into equivalence
classes. But how do we relate those equivalence classes to the terms
of `ℤ₁`?

## Setoids and prequotients

A simple solution would be some function `f : ℤ₂ → ℤ₁`. But it can't
just be _any_ function; it needs to respect the equivalence on
`ℤ₂`. More precisely, `f` must map equivalent elements of `ℤ₂` to the
same element of `ℤ₁`. So we'll need to provide a proof that `f`
behaves as required.

That means we have at least three new concepts to introduce: the
quotient set `ℤ₁`, the mapping function `f`, and the proof that `f`
respects the equivalence on `ℤ₂`. Just as with the definition of
`IsEquivalence`, these concepts have a name when bundled together: a
_prequotient_. Time for some more formalization!

First, we need to introduce a more primitive structure that will serve
as the foundation for our prequotient. We've shown that `ℤ₂` has an
equivalence relation `_≈₂_`, but the knowledge of that is stored in
the parameterized record type `IsEquivalence`, which is somewhat
awkward to deal with in a generic way; if we want to talk abstractly
about _any_ equivalence over an arbitrary set, we have to introduce
variables to plug into the arguments of `IsEquivalence`. Instead, we
can bundle everything together into a single record without
parameters, and this can be dealt with much more
easily. Mathematicians call this object a
[_setoid_](https://en.wikipedia.org/wiki/Setoid), and as the Wikipedia
definition states, it's simply "a set `X` equipped with an equivalence
relation `~`".

```agda
record Setoid : Set₁ where
  field
    A : Set
    _≈_ : Rel₂ A
    isEquiv : IsEquivalence _≈_

open Setoid {{...}}

_respects_ : {A B : Set} → (A → B) → Rel₂ A → Set
f respects _∼_ = ∀ {x y} → x ∼ y → f x ≡ f y

record Prequotient : Set₁ where
  field
    {{S}} : Setoid
    Q : Set
    [_] : A → Q
    sound : [_] respects _≈_
```

There's a lot happening here, so let's unpack it. First, the
definition of `Setoid` makes sense, but what's that `open Setoid
{{...}}` line after it? That's declaring `Setoid` to be available for
use as an [_instance
field_](https://agda.readthedocs.io/en/v2.6.0.1/language/record-types.html#instance-fields)
inside other records. This enables a simple form of subtyping, because
whenever a `Setoid` appears as an instance field in another record,
all of `Setoid`'s fields will be fields of that record as well. And
you can see that we make use of it in `Prequotient`, since it's built
upon the concept of `Setoid`.

Next we define a function `_respects_` which is a convenient shorthand
for the condition that the function `f` mentioned above must
satisfy. We use this in the `Prequotient` record, which defines the
following additional fields on top of `Setoid`:

  - `Q` (the _quotient set_), the type whose elements represent the
    equivalence classes of the `Setoid`;
  - `[_]`, the mapping function that takes an element of the
    `Setoid` and identifies the equivalence class it belongs to; and
  - `sound`, the proof that equivalent elements of the `Setoid` will
    be mapped to the same equivalence class.

And that's all there is to it! Now let's define a `Setoid` and
`Prequotient` for our integer types. The `Setoid` is trivial, since
we've already defined all of its fields:

```agda
ℤ₂-Setoid : Setoid
ℤ₂-Setoid = record { A = ℤ₂ ; _≈_ = _≈₂_ ; isEquiv = ≈₂-IsEquiv }
```

Next is the mapping function:

```agda
[_]₁ : ℤ₂ → ℤ₁
[ ⟨ zero - zero ⟩ ]₁ = ℤ₀
[ ⟨ zero - suc y ⟩ ]₁ = ℤ₋ y
[ ⟨ suc x - zero ⟩ ]₁ = ℤ₊ x
[ ⟨ suc x - suc y ⟩ ]₁ = [ ⟨ x - y ⟩ ]₁
```

It works by normalization. Since a `suc` on both sides of the minus
sign doesn't change the meaning of an integer, we can remove them
until we arrive at one of three base cases, corresponding to a
positive, negative, or zero value. These are directly translatable
into `ℤ₁`.

Those base cases are also important in the soundness proof for the
mapping function. The following lemmas are used in the proof; each one
captures the set of `ℤ₂` values that map onto one of the `ℤ₁` cases.

```agda
[·]₁-refl : ∀ x → [ ⟨ x - x ⟩ ]₁ ≡ ℤ₀
[·]₁-refl zero = refl
[·]₁-refl (suc x) = [·]₁-refl x

[·]₁-right-excess : ∀ x y → [ ⟨ x - x + suc y ⟩ ]₁ ≡ ℤ₋ y
[·]₁-right-excess zero y = refl
[·]₁-right-excess (suc x) y = [·]₁-right-excess x y

[·]₁-left-excess : ∀ x y → [ ⟨ x + suc y - x ⟩ ]₁ ≡ ℤ₊ y
[·]₁-left-excess zero y = refl
[·]₁-left-excess (suc x) y = [·]₁-left-excess x y
```

And now for the soundness proof itself! It's long, but only because
I've used equational reasoning to show the steps a bit more
explicitly.

```agda
[·]₁-sound : (a b : ℤ₂) → a ≈₂ b → [ a ]₁ ≡ [ b ]₁
[·]₁-sound ⟨ a₁ - a₂ ⟩ ⟨ zero - zero ⟩ a₁+0≡a₂+0 =
    begin
      [ ⟨ a₁ - a₂ ⟩ ]₁
    ≡⟨ cong (λ x → [ ⟨ a₁ - x ⟩ ]₁) a₂≡a₁ ⟩
      [ ⟨ a₁ - a₁ ⟩ ]₁
    ≡⟨ [·]₁-refl a₁ ⟩
      ℤ₀
    ≡⟨⟩
      [ ⟨ zero - zero ⟩ ]₁
    ∎
  where
    a₂≡a₁ = sym (+-cancelʳ-≡ a₁ a₂ a₁+0≡a₂+0)
[·]₁-sound ⟨ a₁ - a₂ ⟩ ⟨ zero - suc b₂′ ⟩ a₁+1+b₂′≡a₂+0 =
    begin
      [ ⟨ a₁ - a₂ ⟩ ]₁
    ≡⟨ cong (λ x → [ ⟨ a₁ - x ⟩ ]₁) a₂≡a₁+1+b₂′ ⟩
      [ ⟨ a₁ - a₁ + suc b₂′ ⟩ ]₁
    ≡⟨ [·]₁-right-excess a₁ b₂′ ⟩
      ℤ₋ b₂′
    ≡⟨⟩
      [ ⟨ zero - suc b₂′ ⟩ ]₁
    ∎
  where
    a₂≡a₁+1+b₂′ = sym (trans a₁+1+b₂′≡a₂+0 (+-identityʳ a₂))
[·]₁-sound ⟨ a₁ - a₂ ⟩ ⟨ suc b₁′ - zero ⟩ a₁+0≡a₂+1+b₁′ =
    begin
      [ ⟨ a₁ - a₂ ⟩ ]₁
    ≡⟨ cong (λ x → [ ⟨ x - a₂ ⟩ ]₁) a₁≡a₂+1+b₁′ ⟩
      [ ⟨ a₂ + suc b₁′ - a₂ ⟩ ]₁
    ≡⟨ [·]₁-left-excess a₂ b₁′ ⟩
      ℤ₊ b₁′
    ≡⟨⟩
      [ ⟨ suc b₁′ - zero ⟩ ]₁
    ∎
  where
    a₁≡a₂+1+b₁′ = trans (sym (+-identityʳ a₁)) a₁+0≡a₂+1+b₁′
[·]₁-sound ⟨ a₁ - a₂ ⟩ ⟨ suc b₁′ - suc b₂′ ⟩ a₁+1+b₂′≡a₂+1+b₁′ =
    begin
      [ ⟨ a₁ - a₂ ⟩ ]₁
    ≡⟨ [·]₁-sound ⟨ a₁ - a₂ ⟩ ⟨ b₁′ - b₂′ ⟩ a₁+b₂′≡a₂+b₁′ ⟩
      [ ⟨ b₁′ - b₂′ ⟩ ]₁
    ≡⟨⟩
      [ ⟨ suc b₁′ - suc b₂′ ⟩ ]₁
    ∎
  where
    1+a₁+b₂′≡1+a₂+b₁′ =
      trans (sym (+-suc a₁ b₂′)) (trans a₁+1+b₂′≡a₂+1+b₁′ (+-suc a₂ b₁′))
    a₁+b₂′≡a₂+b₁′ = suc-injective 1+a₁+b₂′≡1+a₂+b₁′
```

The first three cases cover the base cases described above, while the
last one covers the recursive case. In all of them I've used a `where`
clause to hide some of the more tedious type-management behind a
definition; in a more practical proof these would have been handled by
`rewrite` clauses.

Now all that remains is to bundle the definitions up into a
`Prequotient`:

```agda
ℤ₁-Prequotient : Prequotient
ℤ₁-Prequotient =
  record
    { S = ℤ₂-Setoid
    ; Q = ℤ₁
    ; [_] = [_]₁
    ; sound = λ {x y} → [·]₁-sound x y
    }

open Prequotient {{...}}
```

## Simple and definable quotients

We're nearly there! At this point the paper introduces the formal
definition of a quotient, but that definition is a bit complicated for
what we're trying to accomplish. Instead, we're going to use the
paper's second definition of quotient, which introduces some functions
that are actually helpful for our use case. There's no name provided
for this definition, so I've decided to call it `SimpleQuotient`:

```agda
record SimpleQuotient : Set₁ where
  field
    {{PQ}} : Prequotient
    lift : {B : Set} (f : A → B) → f respects _≈_ → Q → B
    lift-β : ∀ {B} f x → (r : f respects _≈_) → lift {B} f r [ x ] ≡ f x
    qind : (P : Q → Set) → ((x : A) → P [ x ]) → (q : Q) → P q
```

What's the significance of these functions? Well, `lift` does what its
name implies: converts a function `f` on the element type `A` to the
quotient type `Q`, so long as `f` respects `A`'s equivalence
relation. The proof `lift-β` ensures that `lift` has the intended
computational behavior: calling `lift f` on `[ x ]` must give the same
result as calling `f` on `x` directly. Finally, `qind` is an induction
principle, which says that if you can show some property `P` holds of
`[ x ]` for all `x : A`, then that property also holds for all `q :
Q`. These will be very helpful when we want to define functions and
proofs on the integers!

However, defining those functions directly seems daunting. Their type
signatures are a bit complex. Luckily, the paper introduces an even
simpler concept, that of a _definable quotient_, and shows how it can
be converted into a `SimpleQuotient`. Here's the definition:

```agda
record DefinableQuotient : Set₁ where
  field
    {{PQ}} : Prequotient
    emb : Q → A
    complete : (a : A) → emb [ a ] ≈ a
    stable : (q : Q) → [ emb q ] ≡ q
```

Yes, you read that correctly; we're simply defining the reverse
mapping of `[_]`, and showing that it preserves both equivalence on
`A` and equality on `Q`. Now to show that this is enough to produce a
`SimpleQuotient`:

```agda
mkSimpleQuotient : DefinableQuotient → SimpleQuotient
mkSimpleQuotient
    record { PQ = PQ ; emb = emb ; complete = complete ; stable = stable } =
      record { PQ = PQ ; lift = lift ; lift-β = lift-β ; qind = qind }
  where
    -- TODO can the renaming be avoided?
    open Prequotient PQ renaming (Q to QQ; [_] to [[_]])

    -- TODO is the proof argument needed here?
    lift : {B : Set} (f : A → B) → f respects _≈_ → QQ → B
    lift f r q = f (emb q)

    lift-β : ∀ {B} f x → (r : f respects _≈_) → lift {B} f r [[ x ]] ≡ f x
    lift-β f x r = r (complete x)

    qind : (P : QQ → Set) → ((x : A) → P [ x ]) → (q : QQ) → P q
    qind P f q = subst P (stable q) (f (emb q))
```

To define `lift`, we simply convert the `Q` value to its corresponding
`A` value, and call `f` on that. For `lift-β`, we use `complete` to
show that `emb [ x ] ≈ x`, and then make use of the `f respects _≈_`
argument to convert that to `f (emb [ x ]) ≡ f x`. This satisfies the
return type because `lift f r [ x ]` reduces to `f (emb [ x ])` by
definition.

Finally, `qind` starts out similar to `lift`: convert `Q` into `A` via
`emb`, then call `f` to obtain a value of type `P [ emb q ]`. From
`stable q` we know that `[ emb q ] ≡ q`, so use `subst` to perform the
rewrite and obtain `P q`.

Now let's create a `DefinableQuotient` for our integer types!

```agda
[_]₂ : ℤ₁ → ℤ₂
[ ℤ₊ x ]₂ = ⟨ suc x - zero ⟩
[ ℤ₀ ]₂ = ⟨ zero - zero ⟩
[ ℤ₋ x ]₂ = ⟨ zero - suc x ⟩

≈₂-suc : ∀ {x y} → ⟨ x - y ⟩ ≈₂ ⟨ suc x - suc y ⟩
≈₂-suc {x} {y} =
  begin
    x + suc y
  ≡⟨ +-suc x y ⟩
    suc (x + y)
  ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x)
  ≡⟨ sym (+-suc y x) ⟩
    y + suc x
  ∎

complete : (a : ℤ₂) → [ [ a ]₁ ]₂ ≈₂ a
complete ⟨ zero - zero ⟩ = refl
complete ⟨ zero - suc a₂ ⟩ = cong suc (sym (+-identityʳ a₂))
complete ⟨ suc a₁ - zero ⟩ = cong suc (+-identityʳ a₁)
complete ⟨ suc a₁ - suc a₂ ⟩ = ≈₂-trans (complete ⟨ a₁ - a₂ ⟩) ≈₂-suc

stable : (q : ℤ₁) → [ [ q ]₂ ]₁ ≡ q
stable (ℤ₊ x) = refl
stable ℤ₀ = refl
stable (ℤ₋ x) = refl

ℤ₁-DefinableQuotient : DefinableQuotient
ℤ₁-DefinableQuotient =
  record
    { PQ = ℤ₁-Prequotient
    ; emb = [_]₂
    ; complete = complete
    ; stable = stable
    }

ℤ₁-SimpleQuotient : SimpleQuotient
ℤ₁-SimpleQuotient = mkSimpleQuotient ℤ₁-DefinableQuotient
```

TODO explain

## Using the quotient

At long last, we can now use our quotient on ℤ₁ to define operations
in terms of ℤ₂:

```agda
-- TODO show that _+₂_ respects _≈₂_

lift₂ : (ℤ₂ → ℤ₂ → ℤ₂) → (ℤ₁ → ℤ₁ → ℤ₁)
lift₂ f p q = [ f [ p ]₂ [ q ]₂ ]₁

_+₁_ : ℤ₁ → ℤ₁ → ℤ₁
_+₁_ = lift₂ _+₂_
```

## Appendix

This is extra stuff from the paper that I haven't gotten around to
explaining yet.

```agda
module _ {{PQ : Prequotient}} where

  compat₂ : {B : Q → Set} → (f : (a : A) → B [ a ]) → Set
  compat₂ {B} f = ∀ {x y} → (r : x ≈ y) → subst B (sound r) (f x) ≡ f y

record Quotient : Set₁ where
  field
    {{PQ}} : Prequotient
    qelim :
      (B : Q → Set) →
      (f : (a : A) → B [ a ]) →
      compat₂ {B} f →
      (q : Q) →
      B q
    qelim-β : ∀ B f → (c : compat₂ f) → ∀ a → qelim B f c [ a ] ≡ f a

record ExactQuotient : Set₁ where
  field QQ : Quotient
  open Quotient QQ public
  field
    exact : {x y : A} → [ x ] ≡ [ y ] → x ≈ y

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

open SimpleQuotient {{...}}

module _ {{SQ : SimpleQuotient}} where

  module _ (P : Q → Set) (p : (x : A) → P [ x ]) (A≈→P≡ : compat₂ p) where
    U : Set
    U = Σ Q P

    p′ : A → U
    p′ x′ = [ x′ ] , p x′

    p′-respects-≈ : p′ respects _≈_
    p′-respects-≈ x≈y = cong-Σ (sound x≈y) (A≈→P≡ x≈y)

    liftU : Q → U
    liftU = lift p′ p′-respects-≈

    liftU-β : ∀ x → liftU [ x ] ≡ p′ x
    liftU-β x = lift-β p′ x p′-respects-≈

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

-- TODO
-- SimpleQuotient→Quotient : SimpleQuotient → Quotient
-- SimpleQuotient→Quotient SQ =
--   record { PQ = SimpleQuotient.PQ SQ ; qelim = qelim₁ SQ ; qelim-β = qelim-β₁ SQ }
```

## Further reading

Here are some sources that helped me out while I was writing this:

1. [Equivalence
   relation](https://en.wikipedia.org/wiki/Equivalence_relation),
   Wikipedia.
1. [Equivalence
   class](https://en.wikipedia.org/wiki/Equivalence_class), Wikipedia.
1. [Quotient Types for
   Programmers](https://www.hedonisticlearning.com/posts/quotient-types-for-programmers.html),
   by Derek Elkins.
