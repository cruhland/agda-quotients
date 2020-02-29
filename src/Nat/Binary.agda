module Nat.Binary where

open import Data.Bool hiding (_≤_; _<_; _<?_)
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Nat.Class
open import Nat.Unary
  using (ℕ₁)
  renaming
    (zero to zero₁
    ; succ to succ₁
    ; _+_ to _+₁_
    ; rec to rec₁
    ; ind to ind₁
    ; rec-succ to rec₁-succ
    )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open ≡-Reasoning

data ℕ₂ : Set where
  zero : ℕ₂
  pos : List Bool → ℕ₂

ind :
  (P : ℕ₂ → Set) →
  P zero →
  P (pos []) →
  (∀ {b bs} → P (pos bs) → P (pos (b ∷ bs))) →
  ∀ n →
  P n
ind P z u d zero = z
ind P z u d (pos []) = u
ind P z u d (pos (b ∷ bs)) = d (ind P z u d (pos bs))

succ⁺ : List Bool → List Bool
succ⁺ [] = false ∷ []
succ⁺ (false ∷ bs) = true ∷ bs
succ⁺ (true ∷ bs) = false ∷ succ⁺ bs

succ : ℕ₂ → ℕ₂
succ zero = pos []
succ (pos bs) = pos (succ⁺ bs)

-- TODO: try to build a rec implementation that computes the
-- predecessor to do unary recursion on binary numbers!  However, the
-- predecessor function must return a proof showing that its result is
-- less than its argument, otherwise Agda doesn't know if the
-- recursion will terminate

digitsFold : {B : Set} → (B → Bool → Bool → B) → B → ℕ₂ → ℕ₂ → B
digitsFold f z zero zero =
  f z false false
digitsFold f z zero (pos []) =
  f z false true
digitsFold f z zero (pos (b₂ ∷ bs₂)) =
  digitsFold f (f z false b₂) zero (pos bs₂)
digitsFold f z (pos []) zero =
  f z true false
digitsFold f z (pos []) (pos []) =
  f z true true
digitsFold f z (pos []) (pos (b₂ ∷ bs₂)) =
  digitsFold f (f z true b₂) zero (pos bs₂)
digitsFold f z (pos (b₁ ∷ bs₁)) zero =
  digitsFold f (f z b₁ false) (pos bs₁) zero
digitsFold f z (pos (b₁ ∷ bs₁)) (pos []) =
  digitsFold f (f z b₁ true) (pos bs₁) zero
digitsFold f z (pos (b₁ ∷ bs₁)) (pos (b₂ ∷ bs₂)) =
  digitsFold f (f z b₁ b₂) (pos bs₁) (pos bs₂)

adder : List Bool × Bool → Bool → Bool → List Bool × Bool
adder (bs , c) a b = (c xor (a xor b)) ∷ bs , (c ∧ (a xor b)) ∨ (a ∧ b)

revNormalize : List Bool → ℕ₂ → ℕ₂
revNormalize [] acc = acc
revNormalize (b ∷ rxs) (pos acc) = revNormalize rxs (pos (b ∷ acc))
revNormalize (false ∷ rxs) zero = revNormalize rxs zero
revNormalize (true ∷ rxs) zero = revNormalize rxs (pos [])

_+_ : ℕ₂ → ℕ₂ → ℕ₂
m + n =
  let rs , c = digitsFold adder ([] , false) m n
   in revNormalize (c ∷ rs) zero

_ : zero + zero ≡ zero
_ =
  begin
    zero + zero
  ≡⟨⟩
    let rs , c = digitsFold adder ([] , false) zero zero
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = adder ([] , false) false false
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs = (false xor (false xor false)) ∷ []
        c = (false ∧ (false xor false)) ∨ (false ∧ false)
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs = false ∷ []
        c = false
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
     revNormalize (false ∷ false ∷ []) zero
  ≡⟨⟩
     revNormalize (false ∷ []) zero
  ≡⟨⟩
     revNormalize [] zero
  ≡⟨⟩
    zero
  ∎

_ : zero + pos [] ≡ pos []
_ =
  begin
    zero + pos []
  ≡⟨⟩
    let rs , c = digitsFold adder ([] , false) zero (pos [])
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = adder ([] , false) false true
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs = (false xor (false xor true)) ∷ []
        c = (false ∧ (false xor true)) ∨ (false ∧ true)
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs = true ∷ []
        c = false
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
     revNormalize (false ∷ true ∷ []) zero
  ≡⟨⟩
     revNormalize (true ∷ []) zero
  ≡⟨⟩
     revNormalize [] (pos [])
  ≡⟨⟩
    pos []
  ∎

_ : zero + pos (false ∷ []) ≡ pos (false ∷ [])
_ =
  begin
    zero + pos (false ∷ [])
  ≡⟨⟩
    let rs , c = digitsFold adder ([] , false) zero (pos (false ∷ []))
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = digitsFold adder (adder ([] , false) false false) zero (pos [])
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let bs′ = (false xor (false xor false)) ∷ []
        c′ = (false ∧ (false xor false)) ∨ (false ∧ false)
        rs , c = digitsFold adder (bs′ , c′) zero (pos [])
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = digitsFold adder (false ∷ [] , false) zero (pos [])
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = adder (false ∷ [] , false) false true
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs = (false xor (false xor true)) ∷ false ∷ []
        c = (false ∧ (false xor true)) ∨ (false ∧ true)
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
     revNormalize (false ∷ true ∷ false ∷ []) zero
  ≡⟨⟩
     revNormalize (true ∷ false ∷ []) zero
  ≡⟨⟩
     revNormalize (false ∷ []) (pos [])
  ≡⟨⟩
     revNormalize [] (pos (false ∷ []))
  ≡⟨⟩
    pos (false ∷ [])
  ∎

-- TODO Expand more zero + n examples
reverse-∷ :
  {A : Set} {x : A} {xs : List A} →
  reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
reverse-∷ {A} {x} {xs} =
  begin
    reverse (x ∷ xs)
  ≡⟨⟩
    foldl (flip _∷_) [] (x ∷ xs)
  ≡⟨⟩
    foldl (flip _∷_) (flip _∷_ [] x) xs
  ≡⟨⟩
    foldl (flip _∷_) (x ∷ []) xs
  ≡⟨ {!!} ⟩
    foldl (flip _∷_) [] xs ++ (x ∷ [])
  ≡⟨⟩
    reverse xs ++ (x ∷ [])
  ∎

reverse-∷-++ :
  {A : Set} {x : A} {xs ys : List A} →
  reverse (x ∷ xs) ++ ys ≡ reverse xs ++ x ∷ ys
reverse-∷-++ {A} {x} {[]} {ys} = refl
reverse-∷-++ {A} {x} {x′ ∷ xs′} {ys} =
  begin
    reverse (x ∷ x′ ∷ xs′) ++ ys
  ≡⟨ {!!} ⟩
    reverse (x′ ∷ xs′) ++ x ∷ ys
  ∎

adder-ca-false : ∀ {b bs} → adder (bs , false) false b ≡ (b ∷ bs , false)
adder-ca-false = refl

digitsFold-adder-zeroˡ-carry :
  ∀ {bs n} → proj₂ (digitsFold adder (bs , false) zero n) ≡ false
digitsFold-adder-zeroˡ-carry {n = zero} = refl
digitsFold-adder-zeroˡ-carry {n = pos []} = refl
digitsFold-adder-zeroˡ-carry {n = pos (b ∷ bs₂)} =
  digitsFold-adder-zeroˡ-carry {n = pos bs₂}

digitsFold-adder-zeroˡ-sum :
  ∀ {rs bs} →
  proj₁ (digitsFold adder (rs , false) zero (pos bs)) ≡ true ∷ reverse bs ++ rs
digitsFold-adder-zeroˡ-sum {rs} {[]} = refl
digitsFold-adder-zeroˡ-sum {rs} {b ∷ bs} =
  begin
    proj₁ (digitsFold adder (rs , false) zero (pos (b ∷ bs)))
  ≡⟨⟩
    proj₁ (digitsFold adder (b ∷ rs , false) zero (pos bs))
  ≡⟨ digitsFold-adder-zeroˡ-sum {b ∷ rs} {bs} ⟩
    true ∷ reverse bs ++ b ∷ rs
  ≡⟨ {!!} ⟩
    true ∷ reverse (b ∷ bs) ++ rs
  ∎

+-identityˡ : ∀ {n} → zero + n ≡ n
+-identityˡ {zero} = refl
+-identityˡ {pos []} = refl
+-identityˡ {pos (b ∷ bs)} =
  begin
    zero + pos (b ∷ bs)
  ≡⟨⟩
    let rs , c = digitsFold adder ([] , false) zero (pos (b ∷ bs))
     in revNormalize (c ∷ rs) zero
  ≡⟨⟩
    let rs , c = digitsFold adder (adder ([] , false) false b) zero (pos bs)
     in revNormalize (c ∷ rs) zero
  ≡⟨ {!!} ⟩
    pos (b ∷ bs)
  ∎

fromℕ₁ : ℕ₁ → ℕ₂
fromℕ₁ = rec₁ zero succ

fromℕ₁-succ : ∀ n → fromℕ₁ (succ₁ n) ≡ succ (fromℕ₁ n)
fromℕ₁-succ zero₁ = refl
fromℕ₁-succ (succ₁ n) =
  begin
    fromℕ₁ (succ₁ (succ₁ n))
  ≡⟨⟩
    rec₁ zero succ (succ₁ (succ₁ n))
  ≡⟨⟩
    rec₁ (succ zero) succ (succ₁ n)
  ≡⟨ rec₁-succ zero succ (succ₁ n) ⟩
    succ (rec₁ zero succ (succ₁ n))
  ≡⟨⟩
    succ (fromℕ₁ (succ₁ n))
  ∎

-- TODO Prove this using algebraic laws!
fromℕ₁-comm-+ : ∀ {m n} → fromℕ₁ (m +₁ n) ≡ fromℕ₁ m + fromℕ₁ n
fromℕ₁-comm-+ {zero₁} {zero₁} = refl
fromℕ₁-comm-+ {zero₁} {succ₁ n} =
  begin
    fromℕ₁ (zero₁ +₁ succ₁ n)
  ≡⟨⟩
    fromℕ₁ (succ₁ n)
  ≡⟨ fromℕ₁-succ n ⟩
    succ (fromℕ₁ n)
  ≡⟨ {!!} ⟩
    zero + succ (fromℕ₁ n)
  ≡⟨ cong (zero +_) (sym (fromℕ₁-succ n)) ⟩
    fromℕ₁ zero₁ + fromℕ₁ (succ₁ n)
  ∎
fromℕ₁-comm-+ {succ₁ m} {n} = {!!}

toℕ₁⁺ : List Bool → ℕ₁
toℕ₁⁺ [] = succ₁ zero₁
toℕ₁⁺ (b ∷ bs) = (if b then succ₁ else id) (toℕ₁⁺ bs +₁ toℕ₁⁺ bs)

toℕ₁ : ℕ₂ → ℕ₁
toℕ₁ zero = zero₁
toℕ₁ (pos bs) = toℕ₁⁺ bs

toℕ₁⁺-succ : ∀ bs → toℕ₁⁺ (succ⁺ bs) ≡ succ₁ (toℕ₁⁺ bs)
toℕ₁⁺-succ [] = refl
toℕ₁⁺-succ (false ∷ bs) = refl
toℕ₁⁺-succ (true ∷ bs) =
  begin
    toℕ₁⁺ (succ⁺ (true ∷ bs))
  ≡⟨⟩
    toℕ₁⁺ (false ∷ succ⁺ bs)
  ≡⟨⟩
    toℕ₁⁺ (succ⁺ bs) +₁ toℕ₁⁺ (succ⁺ bs)
  ≡⟨ cong (λ x → x +₁ toℕ₁⁺ (succ⁺ bs)) (toℕ₁⁺-succ bs) ⟩
    succ₁ (toℕ₁⁺ bs) +₁ toℕ₁⁺ (succ⁺ bs)
  ≡⟨ cong (λ x → succ₁ (toℕ₁⁺ bs) +₁ x) (toℕ₁⁺-succ bs) ⟩
    succ₁ (toℕ₁⁺ bs) +₁ succ₁ (toℕ₁⁺ bs)
  ≡⟨ +-succˡ {m = toℕ₁⁺ bs}  ⟩
    succ₁ (toℕ₁⁺ bs +₁ succ₁ (toℕ₁⁺ bs))
  ≡⟨ cong succ₁ (+-succʳ {m = toℕ₁⁺ bs}) ⟩
    succ₁ (succ₁ (toℕ₁⁺ bs +₁ toℕ₁⁺ bs))
  ≡⟨⟩
    succ₁ (toℕ₁⁺ (true ∷ bs))
  ∎

toℕ₁-succ : ∀ n → toℕ₁ (succ n) ≡ succ₁ (toℕ₁ n)
toℕ₁-succ zero = refl
toℕ₁-succ (pos bs) = toℕ₁⁺-succ bs

fromToℕ₁ : ∀ n → toℕ₁ (fromℕ₁ n) ≡ n
fromToℕ₁ zero₁ = refl
fromToℕ₁ (succ₁ n) =
  begin
    toℕ₁ (fromℕ₁ (succ₁ n))
  ≡⟨ cong toℕ₁ (fromℕ₁-succ n) ⟩
    toℕ₁ (succ (fromℕ₁ n))
  ≡⟨ toℕ₁-succ (fromℕ₁ n) ⟩
    succ₁ (toℕ₁ (fromℕ₁ n))
  ≡⟨ cong succ₁ (fromToℕ₁ n) ⟩
    succ₁ n
  ∎

toFromℕ₁⁺ : ∀ bs → fromℕ₁ (toℕ₁⁺ bs) ≡ pos bs
toFromℕ₁⁺ [] = refl
toFromℕ₁⁺ (false ∷ bs) =
  begin
    fromℕ₁ (toℕ₁⁺ (false ∷ bs))
  ≡⟨⟩
    fromℕ₁ (toℕ₁⁺ bs +₁ toℕ₁⁺ bs)
    -- TODO Fill in these holes!
  ≡⟨ {!!} ⟩
    fromℕ₁ (toℕ₁⁺ bs) + fromℕ₁ (toℕ₁⁺ bs)
  ≡⟨ cong (λ x → x + fromℕ₁ (toℕ₁⁺ bs)) (toFromℕ₁⁺ bs) ⟩
    pos bs + fromℕ₁ (toℕ₁⁺ bs)
  ≡⟨ cong (λ x → pos bs + x) (toFromℕ₁⁺ bs) ⟩
    pos bs + pos bs
  ≡⟨ {!!} ⟩
    pos (false ∷ bs)
  ∎
toFromℕ₁⁺ (true ∷ bs) = {!!}

toFromℕ₁ : ∀ n → fromℕ₁ (toℕ₁ n) ≡ n
toFromℕ₁ zero = refl
toFromℕ₁ (pos bs) = toFromℕ₁⁺ bs

instance
  Nat-ℕ₂ : Nat ℕ₂
  Nat-ℕ₂ = record
    { zero = zero
    ; succ = succ
    ; ind = {!!}
    ; _+_ = _+_
    ; +-zero = +-identityˡ
    ; +-succ = {!!}
    }
