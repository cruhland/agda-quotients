module Nat.Class where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Nat (ℕ : Set) : Set₁ where
  field
    zero : ℕ
    succ : ℕ → ℕ

    ind : (P : ℕ → Set) → P zero → (∀ {k} → P k → P (succ k)) → ∀ n → P n

    _+_ : ℕ → ℕ → ℕ
    +-zero : ∀ {n} → zero + n ≡ n
    +-succ : ∀ {m n} → succ m + n ≡ m + succ n

module _ {ℕ : Set} {{nn : Nat ℕ}} where
  open Nat nn

  +-succˡ : {m n : ℕ} → succ m + n ≡ succ (m + n)
  +-succˡ {m} {n} = ind Succˡ Succˡ-zero Succˡ-succ m n
    where
      Succˡ : ℕ → Set
      Succˡ m′ = ∀ n′ → succ m′ + n′ ≡ succ (m′ + n′)

      Succˡ-zero : Succˡ zero
      Succˡ-zero n′ =
        begin
          succ zero + n′
        ≡⟨ +-succ ⟩
          zero + succ n′
        ≡⟨ +-zero ⟩
          succ n′
        ≡⟨ cong succ (sym +-zero) ⟩
          succ (zero + n′)
        ∎

      Succˡ-succ : ∀ {m′} → Succˡ m′ → Succˡ (succ m′)
      Succˡ-succ {m′} ih n′ =
        begin
          succ (succ m′) + n′
        ≡⟨ +-succ ⟩
          succ m′ + succ n′
        ≡⟨ ih (succ n′) ⟩
          succ (m′ + succ n′)
        ≡⟨ cong succ (sym +-succ) ⟩
          succ (succ m′ + n′)
        ∎

  +-succʳ : {m n : ℕ} → m + succ n ≡ succ (m + n)
  +-succʳ = trans (sym +-succ) +-succˡ

  +-assoc : {m n p : ℕ} → (m + n) + p ≡ m + (n + p)
  +-assoc {m} {n} {p} = ind Assoc Assoc-zero Assoc-succ m
    where
      Assoc : ℕ → Set
      Assoc k = (k + n) + p ≡ k + (n + p)

      Assoc-zero : Assoc zero
      Assoc-zero =
        begin
          (zero + n) + p
        ≡⟨ cong (_+ p) +-zero ⟩
          n + p
        ≡⟨ sym +-zero ⟩
          zero + (n + p)
        ∎

      Assoc-succ : ∀ {k} → Assoc k → Assoc (succ k)
      Assoc-succ {k} ih =
        begin
          (succ k + n) + p
        ≡⟨ cong (_+ p) +-succˡ ⟩
          succ (k + n) + p
        ≡⟨ +-succˡ ⟩
          succ ((k + n) + p)
        ≡⟨ cong succ ih ⟩
          succ (k + (n + p))
        ≡⟨ sym +-succˡ ⟩
          succ k + (n + p)
        ∎
