{-# OPTIONS --without-K --exact-split --safe #-}

module Spartan where

open import Universes public

variable
  U V W T : Universe

data One : El U₀  where
  ⋆ : One

one-ind : (P : One → El U) → P ⋆ → ((x : One) -> P x)
one-ind P a ⋆ = a

one-rec : (B : El U) → B → (One → B)
one-rec B b x = one-ind (λ _ → B) b x

!one : {X : El U} → X → One
!one _ = ⋆

data Zero : El U₀ where

zero-ind : (P : Zero → El U) → ((x : Zero) → P x)
zero-ind P ()


zero-rec : (A : El U) → Zero -> A
zero-rec A z = zero-ind (λ _ → A) z

!zero : (A : El U) → Zero -> A
!zero = zero-rec

is-empty : El U → El U
is-empty X = X → Zero


¬ : El U → El U
¬ = is-empty

data ℕ : El U₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-ind : (P : ℕ → El U) → P 0 → ((n : ℕ) → P n → P (succ n)) → ((n : ℕ) → P n)
ℕ-ind P z s zero = z
ℕ-ind P z s (succ n) = s n (ℕ-ind P z s n)


ℕ-rec : (X : El U) → X → (ℕ → X → X) → (ℕ → X)
ℕ-rec X x sx n = ℕ-ind (λ _ → X) x sx n

ℕ-iter : (X : El U) → X → (X → X) → ℕ → X
ℕ-iter X x sx n = ℕ-rec X x (λ _ → sx) n



